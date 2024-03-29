//! Walks the AST to create a set of type equations that represent the type
//! information of the program.

const std = @import("std");
const scope = @import("scope.zig");
const named = @import("named.zig");
const solver = @import("solver.zig");
const Ast = @import("ast.zig");
const core = @import("core.zig");

const Ty = core.Ty;

pub const TypeBuilder = struct {
    const Self = @This();
    bounds: std.StringHashMapUnmanaged(u16), // inference index
    type_variables: std.StringHashMapUnmanaged(u16), // inference index
    alloc: std.mem.Allocator,

    pub fn init(alloc: std.mem.Allocator) Self {
        return .{ .bounds = .{}, .type_variables = .{}, .alloc = alloc };
    }

    pub fn deinit(self: *Self) void {
        self.bounds.deinit(self.alloc);
        self.type_variables.deinit(self.alloc);
    }

    pub fn boundId(self: *Self, name: []const u8, env: *named.Env) !u16 {
        const get_or_put = try self.bounds.getOrPut(self.alloc, name);
        if (!get_or_put.found_existing) {
            get_or_put.value_ptr.* = try env.addBoundId(name);
        }
        return get_or_put.value_ptr.*;
    }

    pub fn typeVar(self: *Self, name: []const u8, env: *named.Env) !u16 {
        const get_or_put = try self.type_variables.getOrPut(self.alloc, name);
        if (!get_or_put.found_existing) {
            get_or_put.value_ptr.* = try env.variable(.typevar, name);
        }
        return get_or_put.value_ptr.*;
    }
};

pub fn walkDecl(index: u16, ast: *Ast.AST, scope_env: *scope.Env, types: *TypeBuilder, env: *named.Env, equations: *std.ArrayList(solver.Equation)) !void {
    const datas = ast.nodes.items(.data);
    const decl = datas[index].asDecl(index, ast);
    // first, make a definition for the declaration
    const name = try scope_env.define(decl.name, env);

    const impl_scope = try scope_env.createScope(scope_env.current_scope);
    const outer_scope = scope_env.switchToScope(impl_scope);
    defer _ = scope_env.switchToScope(outer_scope);

    // define all clauses names.
    {
        var current_clause = decl.clauses_begin;
        while (current_clause != decl.clauses_end) : (current_clause += 1) {
            const clause_name = datas[current_clause].asDecl(index, ast).name;
            _ = try scope_env.define(clause_name, env);
        }
    }

    // now unveil the patterns
    const lhs = applyDecl: {
        var applied_decl = .{ .inference = name };
        var folded_expr = @as(u16, @truncate(ast.nodes.len));
        try ast.nodes.append(ast.alloc, .{
            .tag = .name_lookup,
            .data = .{ .lhs = ast.decl_infos.items[datas[index].lhs].name_index, .rhs = 0 },
        });
        var current_arg = decl.args_begin;
        try equations.ensureUnusedCapacity(decl.args_end - decl.args_begin);
        try ast.nodes.ensureUnusedCapacity(ast.alloc, decl.args_end - decl.args_begin);
        while (current_arg != decl.args_end) : (current_arg += 1) {
            const arg_ty = try walkPattern(current_arg, ast, scope_env, types, env, equations);

            const applied_folded_expr = mkApplyExpr: {
                const res = @as(u16, @truncate(ast.nodes.len));
                ast.nodes.appendAssumeCapacity(Ast.Node.apply(folded_expr, current_arg));
                break :mkApplyExpr res;
            };

            const ret = try env.expr(applied_folded_expr);
            const equation = try apply(applied_decl, arg_ty, .{ .inference = ret }, types, env);
            equations.appendAssumeCapacity(equation);
            applied_decl = .{ .inference = ret };
            folded_expr = applied_folded_expr;
        }
        break :applyDecl applied_decl;
    };

    // now that we've declared all the names we can use (both from clauses and patterns),
    // process the clauses and the right hand side of the equation.
    {
        var current_clause = decl.clauses_begin;
        while (current_clause != decl.clauses_end) : (current_clause += 1) {
            try walkDecl(current_clause, ast, scope_env, types, env, equations);
        }
    }

    const rhs = try walkExpr(decl.expr, ast, scope_env, types, env, equations);

    try equations.append(.{ .lhs = lhs, .rhs = rhs });
}

/// patterns are like expressions plus the bind. Except that they 'unwrap' the expression instead of wrapping it.
/// To produce equations, it returns the type that would be after the construction has occurred.
fn walkPattern(index: u16, ast: *const Ast.AST, scope_env: *scope.Env, types: *TypeBuilder, env: *named.Env, equations: *std.ArrayList(solver.Equation)) !Ty {
    switch (ast.nodes.items(.tag)[index]) {
        // a 'lookup' in pattern context just means that we're defining a variable
        // well, not really. It might be also used for applying constructors that need to be a lookup...
        .name_lookup => {
            const name_index = ast.nodes.items(.data)[index].asRef();
            const name = ast.asName(name_index);
            const inference_index = try scope_env.define(name, env);
            return .{ .inference = inference_index };
        },
        // a binding is like a lookup but we first walk the pattern and equate the variable
        // to the construction of that whole pattern.
        .bind => {
            const info = ast.nodes.items(.data)[index].asBind(ast);
            const name_inference = try scope_env.define(info.name, env);
            const pattern_ty = try walkPattern(info.expr, ast, scope_env, types, env, equations);
            // equate both sides since their types are *exactly* the same.
            try equations.append(.{ .lhs = .{ .inference = name_inference }, .rhs = pattern_ty });
            return .{ .inference = name_inference };
        },
        // an application is resolved the same way as an expression but through the context of patterns
        .apply => {
            const info = ast.nodes.items(.data)[index].asApply();
            const func = if (ast.nodes.items(.tag)[info.func] == .name_lookup)
                Ty{ .inference = try scope_env.define(ast.asName(ast.nodes.items(.data)[info.func].asRef()), env) }
            else
                try walkPattern(info.func, ast, scope_env, types, env, equations);
            const arg = try walkPattern(info.arg, ast, scope_env, types, env, equations);

            // define a new type to be the result of this application
            // (currently an 'unknown' but I'll develop something for it)
            const res = .{ .inference = try env.expr(index) };
            const eq = try apply(func, arg, res, types, env);
            try equations.append(eq);

            // the resulting type of the pattern is the full application of the constructor
            return res;
        },

        // a value that is ignored will just get a new inference that will be adjusted
        // as needed.
        .ignored => {
            return .{ .inference = try scope_env.unknown(env) };
        },

        else => unreachable,
    }
}

fn walkExpr(index: u16, ast: *const Ast.AST, scope_env: *scope.Env, types: *TypeBuilder, env: *named.Env, equations: *std.ArrayList(solver.Equation)) !Ty {
    switch (ast.nodes.items(.tag)[index]) {
        .name_lookup => {
            const name_index = ast.nodes.items(.data)[index].asRef();
            const name = ast.asName(name_index);
            const inference_ty = try scope_env.get(name, env);
            return inference_ty;
        },
        .apply => {
            const info = ast.nodes.items(.data)[index].asApply();
            const func = try walkExpr(info.func, ast, scope_env, types, env, equations);
            const arg = try walkExpr(info.arg, ast, scope_env, types, env, equations);
            const res = .{ .inference = try env.expr(index) };
            try equations.ensureUnusedCapacity(1);
            const eq = try apply(func, arg, res, types, env);
            equations.appendAssumeCapacity(eq);
            return res;
        },
        .ifexpr => {
            const info = ast.nodes.items(.data)[index].asIf(index, ast);
            const if_inference = Ty{ .inference = try env.expr(index) };
            const condition = try walkExpr(info.condition, ast, scope_env, types, env, equations);
            const then_part = try walkExpr(info.then_part, ast, scope_env, types, env, equations);
            const else_part = try walkExpr(info.else_part, ast, scope_env, types, env, equations);
            const bool_ty = .{ .bound = .{ .id = try types.boundId("Bool", env), .range = core.Range.empty() } };
            try equations.ensureUnusedCapacity(3);
            // condition must be bool
            equations.appendAssumeCapacity(.{ .lhs = condition, .rhs = bool_ty });
            // both sides of the branch must result in the same type
            equations.appendAssumeCapacity(.{ .lhs = if_inference, .rhs = then_part });
            equations.appendAssumeCapacity(.{ .lhs = if_inference, .rhs = else_part });
            return if_inference;
        },
        else => unreachable,
    }
}

fn apply(a: Ty, b: Ty, res: Ty, types: *TypeBuilder, env: *named.Env) !solver.Equation {
    try env.core_env.tys.ensureUnusedCapacity(env.alloc, 2);
    const bound_id = try types.boundId("(->)", env);
    const start = @as(u16, @truncate(env.core_env.tys.items.len));
    env.core_env.tys.appendAssumeCapacity(b);
    env.core_env.tys.appendAssumeCapacity(res);
    const applied = Ty{ .bound = .{
        .id = bound_id,
        .range = .{ .start = start, .end = start + 2 },
    } };
    return .{ .lhs = a, .rhs = applied };
}
