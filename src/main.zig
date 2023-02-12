const std = @import("std");

const core = @import("core.zig");
const solver = @import("solver.zig");
const named = @import("named.zig");
const Ast = @import("ast.zig");

const log = std.log.scoped(.main);

const Ty = core.Ty;

fn drop_temps(inferences: *solver.Map, env: *const named.Env) !void {
    var dropped = std.ArrayList(u16).init(inferences.allocator);
    defer {
        for (dropped.items) |dropped_k| {
            _ = inferences.remove(dropped_k);
        }
        dropped.deinit();
    }

    var keys = inferences.keyIterator();
    while (keys.next()) |k| {
        const tag = env.inferences.items[k.*].tag;
        if (tag != .variable) {
            try dropped.append(k.*);
        }
    }
}

fn format_inferences(writer: anytype, inferences: *const solver.Map, env: *const named.Env, ast: *const Ast.AST) !void {
    _ = try writer.write("inferences:\n");
    var it = inferences.iterator();
    while (it.next()) |entry| {
        try Ast.format_ty(writer, .{ .inference = entry.key_ptr.* }, env, ast);
        _ = try writer.write(" :: ");
        try Ast.format_ty(writer, entry.value_ptr.*, env, ast);
        _ = try writer.write("\n");
    }
}

fn format_error(writer: anytype, err: solver.Error, env: *const named.Env, ast: *const Ast.AST) !void {
    switch (err) {
        .cyclic_type => |ty| {
            _ = try writer.write("cyclic type: ");
            try Ast.format_ty(writer, ty, env, ast);
        },
        .unequal_bounds => |eq| {
            _ = try writer.write("Cannot equate ");
            try Ast.format_ty(writer, eq.lhs, env, ast);
            _ = try writer.write(" to ");
            try Ast.format_ty(writer, eq.rhs, env, ast);
        },
    }
}

fn format_result(writer: anytype, results: *const solver.Result, env: *const named.Env, ast: *const Ast.AST) !void {
    _ = try writer.write("errors:\n");
    for (results.errors.items) |err| {
        try format_error(writer, err, env, ast);
        _ = try writer.write("\n");
    }

    try format_inferences(writer, &results.inferences, env, ast);
}

// NOTE: consider using unmanaged for this, since we're duplicating the allocator
const TypeBuilder = struct {
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

    pub fn bound_id(self: *Self, name: []const u8, env: *named.Env) !u16 {
        const get_or_put = try self.bounds.getOrPut(self.alloc, name);
        if (!get_or_put.found_existing) {
            get_or_put.value_ptr.* = try env.add_bound_id(name);
        }
        return get_or_put.value_ptr.*;
    }

    pub fn type_var(self: *Self, name: []const u8, env: *named.Env) !u16 {
        const get_or_put = try self.type_variables.getOrPut(self.alloc, name);
        if (!get_or_put.found_existing) {
            get_or_put.value_ptr.* = try env.variable(.typevar, name);
        }
        return get_or_put.value_ptr.*;
    }
};

const ScopeEnv = struct {
    const Self = @This();

    const HintMap = std.StringHashMapUnmanaged(Ty);
    pub fn format_hintmap(self: *const Self, w: anytype, ast: *const Ast.AST, env: *const named.Env) void {
        std.fmt.format(w, "hints in current scope:\n", .{}) catch {};
        var iter = self.scopes.items[self.current_scope].hints.iterator();
        while (iter.next()) |i| {
            std.fmt.format(w, "{s} = ", .{i.key_ptr.*}) catch {};
            Ast.format_ty(w, i.value_ptr.*, env, ast) catch {};
            std.fmt.format(w, "\n", .{}) catch {};
        }
    }

    const Scope = struct {
        parent: ?ScopeIndex,
        hints: HintMap,
        variables: std.StringHashMapUnmanaged(u16), // inference index

        pub fn deinit(self: *Scope, alloc: std.mem.Allocator) void {
            self.variables.deinit(alloc);
            self.hints.deinit(alloc);
        }

        pub fn define(self: *Scope, name: []const u8, env: *named.Env, alloc: std.mem.Allocator) !u16 {
            const get_or_put = try self.variables.getOrPut(alloc, name);

            // if we had another definition, reuse that index instead of wasting space.
            // this way we can also point all definitions of the inference to the new set,
            // so that things declared initially as 'unknown' get redirected to the new sample.
            if (!get_or_put.found_existing) {
                const inf = try env.create_var(.variable, name);
                const new_inference = try env.inference(inf);
                get_or_put.value_ptr.* = new_inference;
            }

            return get_or_put.value_ptr.*;
        }
    };

    const ScopeIndex = u8;

    current_scope: ScopeIndex,
    scopes: std.ArrayListUnmanaged(Scope),
    arena: std.heap.ArenaAllocator,

    // NOTE: currently there is only one unknown counter
    unknown_count: u14,

    pub fn init(alloc: std.mem.Allocator) Self {
        return .{ .current_scope = 0, .scopes = .{}, .unknown_count = 0, .arena = std.heap.ArenaAllocator.init(alloc) };
    }

    pub fn deinit(self: *Self) void {
        var ally = self.arena.allocator();

        var i: usize = 0;
        while (i != self.scopes.items.len) : (i += 1) {
            self.scopes.items[i].deinit(ally);
        }

        self.scopes.deinit(ally);
        self.arena.deinit();
    }

    pub fn create_scope(self: *Self, parent: ?ScopeIndex) !ScopeIndex {
        const len = @truncate(ScopeIndex, self.scopes.items.len);
        try self.scopes.append(self.arena.allocator(), .{ .parent = parent, .variables = .{}, .hints = .{} });
        return len;
    }

    // NOTE: this is currently replacing stuff resulting from expressions
    pub fn unknown(self: *Self, env: *named.Env) !u16 {
        const inference_index = try env.unknown(self.unknown_count);
        self.unknown_count += 1;
        return inference_index;
    }

    pub fn switch_to_scope(self: *Self, scope: ScopeIndex) ScopeIndex {
        const old_scope = self.current_scope;
        self.current_scope = scope;
        return old_scope;
    }

    pub fn add_hint(self: *Self, name: []const u8, ty: Ty) !void {
        try self.scopes.items[self.current_scope].hints.put(self.arena.allocator(), name, ty);
    }

    pub fn get(self: *Self, name: []const u8, env: *named.Env) !Ty {
        const found_inference = getvar: {
            var current_scope: *Scope = &self.scopes.items[self.current_scope];
            break :getvar while (true) {
                if (current_scope.variables.get(name)) |n| break n;
                if (current_scope.parent) |p| {
                    current_scope = &self.scopes.items[p];
                } else break null;
            };
        };

        const final_inference = if (found_inference) |i| Ty{ .inference = i } else instantiate_unknown: {
            const found_hint = gethint: {
                var current_scope = self.current_scope;
                break :gethint while (true) {
                    if (self.scopes.items[current_scope].hints.get(name)) |h|
                        break h;
                    if (self.scopes.items[current_scope].parent) |p| {
                        current_scope = p;
                    } else break null;
                };
            };

            break :instantiate_unknown if (found_hint) |hint| try env.instantiate(hint) else Ty{ .inference = try env.variable(.variable, name) };
        };

        return final_inference;
    }

    pub fn define(self: *Self, name: []const u8, env: *named.Env) !u16 {
        return try self.scopes.items[self.current_scope].define(name, env, self.arena.allocator());
    }
};

fn apply(a: Ty, b: Ty, res: Ty, types: *TypeBuilder, env: *named.Env) !solver.Equation {
    try env.core_env.tys.ensureUnusedCapacity(env.alloc, 2);
    const bound_id = try types.bound_id("(->)", env);
    const start = @truncate(u16, env.core_env.tys.items.len);
    env.core_env.tys.appendAssumeCapacity(b);
    env.core_env.tys.appendAssumeCapacity(res);
    const applied = Ty{ .bound = .{
        .id = bound_id,
        .range = .{ .start = start, .end = start + 2 },
    } };
    return .{ .lhs = a, .rhs = applied };
}

fn walk_expr(index: u16, ast: *const Ast.AST, scope_env: *ScopeEnv, types: *TypeBuilder, env: *named.Env, equations: *std.ArrayList(solver.Equation)) !Ty {
    switch (ast.nodes.items(.tag)[index]) {
        .name_lookup => {
            const name_index = ast.nodes.items(.data)[index].as_ref();
            const name = ast.as_name(name_index);
            const inference_ty = try scope_env.get(name, env);
            return inference_ty;
        },
        .apply => {
            const info = ast.nodes.items(.data)[index].as_apply();
            const func = try walk_expr(info.func, ast, scope_env, types, env, equations);
            const arg = try walk_expr(info.arg, ast, scope_env, types, env, equations);
            const res = .{ .inference = try env.expr(index) };
            try equations.ensureUnusedCapacity(1);
            const eq = try apply(func, arg, res, types, env);
            equations.appendAssumeCapacity(eq);
            return res;
        },
        .ifexpr => {
            const info = ast.nodes.items(.data)[index].as_if(index, ast);
            const if_inference = Ty{ .inference = try env.expr(index) };
            const condition = try walk_expr(info.condition, ast, scope_env, types, env, equations);
            const then_part = try walk_expr(info.then_part, ast, scope_env, types, env, equations);
            const else_part = try walk_expr(info.else_part, ast, scope_env, types, env, equations);
            const bool_ty = .{ .bound = .{ .id = try types.bound_id("Bool", env), .range = core.Range.empty() } };
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

// patterns are like expressions plus the bind. Except that they 'unwrap' the expression instead of wrapping it.
// To produce equations, it returns the type that would be after the construction has occurred.
fn walk_pattern(index: u16, ast: *const Ast.AST, scope_env: *ScopeEnv, types: *TypeBuilder, env: *named.Env, equations: *std.ArrayList(solver.Equation)) !Ty {
    switch (ast.nodes.items(.tag)[index]) {
        // a 'lookup' in pattern context just means that we're defining a variable
        // well, not really. It might be also used for applying constructors that need to be a lookup...
        .name_lookup => {
            const name_index = ast.nodes.items(.data)[index].as_ref();
            const name = ast.as_name(name_index);
            const inference_index = try scope_env.define(name, env);
            return .{ .inference = inference_index };
        },
        // a binding is like a lookup but we first walk the pattern and equate the variable
        // to the construction of that whole pattern.
        .bind => {
            const info = ast.nodes.items(.data)[index].as_bind(ast);
            const name_inference = try scope_env.define(info.name, env);
            const pattern_ty = try walk_pattern(info.expr, ast, scope_env, types, env, equations);
            // equate both sides since their types are *exactly* the same.
            try equations.append(.{ .lhs = .{ .inference = name_inference }, .rhs = pattern_ty });
            return .{ .inference = name_inference };
        },
        // an application is resolved the same way as an expression but through the context of patterns
        .apply => {
            const info = ast.nodes.items(.data)[index].as_apply();
            // if the function is a lookup, use 'get', not 'define', which would be used in `walk_pattern`.
            const func = if (ast.nodes.items(.tag)[info.func] == .name_lookup)
                try scope_env.get(ast.as_name(ast.nodes.items(.data)[info.func].as_ref()), env)
            else
                try walk_pattern(info.func, ast, scope_env, types, env, equations);
            const arg = try walk_pattern(info.arg, ast, scope_env, types, env, equations);

            try equations.ensureUnusedCapacity(1);

            // define a new type to be the result of this application
            // (currently an 'unknown' but I'll develop something for it)
            const res = .{ .inference = try env.expr(index) };
            const eq = try apply(func, arg, res, types, env);
            equations.appendAssumeCapacity(eq);

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

fn walk_decl(index: u16, ast: *Ast.AST, scope_env: *ScopeEnv, types: *TypeBuilder, env: *named.Env, equations: *std.ArrayList(solver.Equation)) !void {
    const datas = ast.nodes.items(.data);
    const decl = datas[index].as_decl(index, ast);
    // first, make a definition for the declaration
    const name = try scope_env.define(decl.name, env);

    const impl_scope = try scope_env.create_scope(scope_env.current_scope);
    const outer_scope = scope_env.switch_to_scope(impl_scope);
    defer _ = scope_env.switch_to_scope(outer_scope);

    // define all clauses names.
    {
        var current_clause = decl.clauses_begin;
        while (current_clause != decl.clauses_end) : (current_clause += 1) {
            const clause_name = datas[current_clause].as_decl(index, ast).name;
            _ = try scope_env.define(clause_name, env);
        }
    }

    // now unveil the patterns
    const lhs = apply_decl: {
        var applied_decl = .{ .inference = name };
        var folded_expr = @truncate(u16, ast.nodes.len);
        try ast.nodes.append(ast.alloc, .{
            .tag = .name_lookup,
            .data = .{ .lhs = ast.decl_infos.items[datas[index].lhs].name_index, .rhs = 0 },
        });
        var current_arg = decl.args_begin;
        try equations.ensureUnusedCapacity(decl.args_end - decl.args_begin);
        while (current_arg != decl.args_end) : (current_arg += 1) {
            const arg_ty = try walk_pattern(current_arg, ast, scope_env, types, env, equations);

            const applied_folded_expr = mkApplyExpr: {
                const res = @truncate(u16, ast.nodes.len);
                try ast.nodes.append(ast.alloc, .{
                    .tag = .apply,
                    .data = .{ .lhs = folded_expr, .rhs = current_arg },
                });
                break :mkApplyExpr res;
            };

            const ret = try env.expr(applied_folded_expr);
            const equation = try apply(applied_decl, arg_ty, .{ .inference = ret }, types, env);
            equations.appendAssumeCapacity(equation);
            applied_decl = .{ .inference = ret };
            folded_expr = applied_folded_expr;
        }
        break :apply_decl applied_decl;
    };

    // now that we've declared all the names we can use (both from clauses and patterns),
    // process the clauses and the right hand side of the equation.
    {
        var current_clause = decl.clauses_begin;
        while (current_clause != decl.clauses_end) : (current_clause += 1) {
            try walk_decl(current_clause, ast, scope_env, types, env, equations);
        }
    }

    const rhs = try walk_expr(decl.expr, ast, scope_env, types, env, equations);

    try equations.append(.{ .lhs = lhs, .rhs = rhs });
}

fn format_constraints(writer: anytype, constraints: []const solver.Equation, env: *const named.Env, ast: *const Ast.AST) !void {
    for (constraints) |c| {
        try Ast.format_ty(writer, c.lhs, env, ast);
        _ = try writer.write(" = ");
        try Ast.format_ty(writer, c.rhs, env, ast);
        _ = try writer.write("\n");
    }
}

const Input = struct {
    all: []const u8,
    start: u32,

    pub fn init(input: []const u8) Input {
        return .{ .all = input, .start = 0 };
    }

    pub fn eof(self: *Input) bool {
        return self.start == self.all.len;
    }

    pub fn accept(self: *Input) void {
        self.start += 1;
    }
};

const ASTBuilder = struct {
    const Self = @This();

    pub const NameInfo = struct { lookup_node: u16, name_index: u16 };

    ast: *Ast.AST,
    name_cache: std.StringHashMapUnmanaged(NameInfo),
    // the Ast.AST and the Parser have distinct allocs since the parser cache will be
    // cleaned right after we're done with parsing.
    alloc: std.mem.Allocator,

    pub fn init(alloc: std.mem.Allocator, ast: *Ast.AST) Self {
        return .{ .ast = ast, .name_cache = .{}, .alloc = alloc };
    }

    pub fn cachedNameAssumeCapacity(self: *Self, name: []const u8) NameInfo {
        const get_or_put = self.lookup_node_cache.getOrPutAssumeCapacity(name);
        if (!get_or_put.found_existing) {
            const index = @truncate(u16, self.ast.names.len);
            self.ast.names.appendAssumeCapacity(name);
            const node = self.ast.nameAssumeCapacity(index);
            const info = NameInfo{ .lookup_node = node, .name_index = index };
            get_or_put.value_ptr.* = info;
            return info;
        } else {
            return get_or_put.value_ptr.*;
        }
    }

    pub fn cachedName(self: *Self, name: []const u8) !NameInfo {
        const get_or_put = try self.name_cache.getOrPut(self.alloc, name);
        if (!get_or_put.found_existing) {
            const index = @truncate(u16, self.ast.names.items.len);
            try self.ast.names.append(name);
            const node = try self.ast.name(index);
            const info = NameInfo{ .lookup_node = node, .name_index = index };
            get_or_put.value_ptr.* = info;
            return info;
        } else {
            return get_or_put.value_ptr.*;
        }
    }

    pub fn deinit(self: *Self) void {
        self.name_cache.deinit(self.alloc);
    }
};

fn build_unify_2(builder: *ASTBuilder) !u16 {
    // unify (Inference a) k = if occurs a k then Left (CyclicType k) else Right
    // (Infer a k)

    const a = try builder.cachedName("a");
    const inference_lookup = try builder.cachedName("Inference");
    const k = try builder.cachedName("k");
    const left = try builder.cachedName("Left");
    const cyclic_type = try builder.cachedName("CyclicType");
    const infer = try builder.cachedName("Infer");
    const right = try builder.cachedName("Right");
    const occurs_ = try builder.cachedName("occurs");
    const unify = try builder.cachedName("unify");

    const else_part = try builder.ast.apply(
        right.lookup_node,
        try builder.ast.apply(try builder.ast.apply(infer.lookup_node, a.lookup_node), k.lookup_node),
    );

    const then_part = try builder.ast.apply(
        left.lookup_node,
        try builder.ast.apply(cyclic_type.lookup_node, k.lookup_node),
    );

    const condition = try builder.ast.apply(try builder.ast.apply(occurs_.lookup_node, a.lookup_node), k.lookup_node);

    const res = try builder.ast.pushIf(condition, then_part, else_part);

    // I need two fresh nodes here
    const arg0 = Ast.AST.Node.apply(inference_lookup.lookup_node, a.lookup_node);
    const arg1 = Ast.AST.Node.lookup(k.name_index);

    return try builder.ast.decl(unify.name_index, &.{ arg0, arg1 }, res, &.{});
}

fn build_unify_1(ast: *Ast.AST) !u16 {

    // unify (Inference a) (Inference b) =
    //  if a == b then Right Empty else Right (Infer a (Inference b))

    try ast.nodes.ensureUnusedCapacity(ast.alloc, 19);
    try ast.ifs.ensureUnusedCapacity(1);
    try ast.decl_infos.ensureUnusedCapacity(1);

    try ast.names.ensureUnusedCapacity(8);
    const right_name_index = @truncate(u16, ast.names.items.len);

    const right_lookup = ast.pushNodeAssumeCapacity(.{
        .tag = .name_lookup,
        .data = .{ .lhs = right_name_index, .rhs = 0 },
    });

    const empty_name_index = @truncate(u16, ast.names.items.len + 1);
    const b_name_index = @truncate(u16, ast.names.items.len + 2);
    const inference_name_index = @truncate(u16, ast.names.items.len + 3);
    const infer_name_index = @truncate(u16, ast.names.items.len + 4);
    const a_name_index = @truncate(u16, ast.names.items.len + 5);

    const a_lookup = ast.nameAssumeCapacity(a_name_index);

    const b_lookup = ast.nameAssumeCapacity(b_name_index);

    const inference_lookup = ast.nameAssumeCapacity(inference_name_index);

    const eq_name_index = @truncate(u16, ast.names.items.len + 6);
    const unify_name_index = @truncate(u16, ast.names.items.len + 7);

    ast.names.appendSliceAssumeCapacity(&[_][]const u8{ "Right", "Empty", "b", "Inference", "Infer", "a", "(==)", "unify" });

    // Right Empty
    const then_part = ast.applyAssumeCapacity(
        right_lookup,
        ast.nameAssumeCapacity(empty_name_index),
    );

    // (Inference b)
    const inference_b = ast.applyAssumeCapacity(inference_lookup, b_lookup);

    // Right (Infer a (Inference b))
    const else_part = ast.applyAssumeCapacity(
        right_lookup,
        ast.applyAssumeCapacity(ast.applyAssumeCapacity(
            ast.nameAssumeCapacity(infer_name_index),
            a_lookup,
        ), inference_b),
    );

    // ((==) a) b
    const condition = ast.applyAssumeCapacity(ast.applyAssumeCapacity(
        ast.nameAssumeCapacity(eq_name_index),
        a_lookup,
    ), b_lookup);

    // if a == b then Right Empty else Right (Infer a (Inference b))
    const unify_res = ast.pushIfAssumeCapacity(condition, then_part, else_part);

    return ast.declAssumeCapacity(unify_name_index, &.{
        .{ .tag = .apply, .data = .{ .lhs = inference_lookup, .rhs = a_lookup } },
        .{ .tag = .apply, .data = .{ .lhs = inference_lookup, .rhs = b_lookup } },
    }, unify_res, &.{});
}

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();

    var arena = std.heap.ArenaAllocator.init(gpa.allocator());
    defer _ = arena.deinit();

    var env = named.Env.init(arena.allocator());
    defer env.deinit();

    var ast = Ast.AST.init(arena.allocator());
    defer ast.deinit();

    var ty_builder = TypeBuilder.init(arena.allocator());
    defer ty_builder.deinit();

    // ScopeEnv creates its own arena allocator so I'll just give it GPA.
    var scope_env = ScopeEnv.init(gpa.allocator());
    defer scope_env.deinit();

    // root
    _ = try scope_env.create_scope(null);

    // stdout is for the actual output of your application, for example if you
    // are implementing gzip, then only the compressed bytes should be sent to
    // stdout, not any debugging messages.
    const stdout_file = std.io.getStdOut().writer();
    var bw = std.io.bufferedWriter(stdout_file);
    const stdout = bw.writer();

    // add hint: (==) :: a -> a -> Bool
    {
        const a_typevar = Ty{ .inference = try env.variable(.typevar, "a") };
        const e_typevar = Ty{ .inference = try env.variable(.typevar, "e") };
        const bool_ty = Ty{ .bound = .{ .id = try ty_builder.bound_id("Bool", &env), .range = core.Range.empty() } };
        const func_bound_id = try ty_builder.bound_id("(->)", &env);

        const unify_event_a = build_unify_ev: {
            const start = try env.core_env.insert_ty(env.alloc, a_typevar);
            break :build_unify_ev Ty{ .bound = .{
                .id = try ty_builder.bound_id("UnifyEvent", &env),
                .range = .{ .start = start, .end = start + 1 },
            } };
        };

        const unify_error_a = build_unify_err: {
            const start = try env.core_env.insert_ty(env.alloc, a_typevar);
            break :build_unify_err Ty{ .bound = .{ .id = try ty_builder.bound_id("UnifyError", &env), .range = .{ .start = start, .end = start + 1 } } };
        };

        const either_e_a = build_either: {
            const bound_id = try ty_builder.bound_id("Either", &env);
            const start = try env.core_env.insert_ty(env.alloc, e_typevar);
            _ = try env.core_env.insert_ty(env.alloc, a_typevar);
            break :build_either Ty{ .bound = .{
                .id = bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        };

        //        try scope_env.add_hint("Empty", unify_event_a);

        try scope_env.add_hint("Right", mkRight: {
            const start = try env.core_env.insert_ty(env.alloc, a_typevar);
            _ = try env.core_env.insert_ty(env.alloc, either_e_a);
            break :mkRight .{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        });

        try scope_env.add_hint("Left", mkLeft: {
            const start = try env.core_env.insert_ty(env.alloc, e_typevar);
            _ = try env.core_env.insert_ty(env.alloc, either_e_a);
            break :mkLeft .{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        });

        //const list_bound_id = try ty_builder.bound_id("[]", &env);

        {
            const a2bool = a2bool: {
                const start = try env.core_env.insert_ty(env.alloc, a_typevar);
                _ = try env.core_env.insert_ty(env.alloc, bool_ty);
                break :a2bool Ty{ .bound = .{ .id = func_bound_id, .range = .{ .start = start, .end = start + 2 } } };
            };

            const eq = eq: {
                const start = try env.core_env.insert_ty(env.alloc, a_typevar);
                _ = try env.core_env.insert_ty(env.alloc, a2bool);
                break :eq Ty{ .bound = .{ .id = func_bound_id, .range = .{ .start = start, .end = start + 2 } } };
            };

            try scope_env.add_hint("(==)", eq);
        }

        const inference_ty_id = try ty_builder.bound_id("InferenceTy", &env);

        const inference_ty_a = inference_ty: {
            const start = try env.core_env.insert_ty(env.alloc, a_typevar);
            break :inference_ty Ty{ .bound = .{
                .id = inference_ty_id,
                .range = .{ .start = start, .end = start + 1 },
            } };
        };
        try scope_env.add_hint("CyclicType", mkCT: {
            const start = try env.core_env.insert_ty(env.alloc, inference_ty_a);
            _ = try env.core_env.insert_ty(env.alloc, unify_error_a);
            break :mkCT .{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        });

        try scope_env.add_hint("Infer", build_infer: {
            // InferenceTy a -> UnifyEvent a
            const middle_param = try env.core_env.insert_ty(env.alloc, inference_ty_a);
            _ = try env.core_env.insert_ty(env.alloc, unify_event_a);

            // a -> (InferenceTy a -> UnifyEvent a)
            const start = try env.core_env.insert_ty(env.alloc, a_typevar);
            _ = try env.core_env.insert_ty(env.alloc, .{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = middle_param, .end = middle_param + 2 },
            } });
            break :build_infer Ty{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        });

        try scope_env.add_hint("Inference", inference: {
            const start = try env.core_env.insert_ty(env.alloc, a_typevar);
            _ = try env.core_env.insert_ty(env.alloc, inference_ty_a);
            break :inference .{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        });

        //        const list_of_inference_ty_a = mklist: {
        //            const start = try env.core_env.insert_ty(env.alloc, inference_ty_a);
        //            break :mklist Ty{ .bound = .{ .bound_id = list_bound_id, .bound_range = .{ .start = start, .end = start + 1 } } };
        //        };
        //
        //        try scope_env.add_hint("Bound", mkBound: {
        //            const func_list_to_a = mkList2a: {
        //                const start = try env.core_env.insert_ty(env.alloc, list_of_inference_ty_a);
        //                _ = try env.core_env.insert_ty(env.alloc, inference_ty_a);
        //                break :mkList2a Ty{ .bound = .{
        //                    .bound_id = func_bound_id,
        //                    .bound_range = .{ .start = start, .end = start + 2 },
        //                } };
        //            };
        //
        //            const start = try env.core_env.insert_ty(env.alloc, a_typevar);
        //            _ = try env.core_env.insert_ty(env.alloc, func_list_to_a);
        //            break :mkBound .{ .bound = .{
        //                .bound_id = func_bound_id,
        //                .bound_range = .{ .start = start, .end = start + 2 },
        //            } };
        //        });
    }

    scope_env.format_hintmap(stdout, &ast, &env);

    // constraints also go into GPA since its allocations are sporadic.
    var constraints = std.ArrayList(solver.Equation).init(gpa.allocator());

    const unify_1_index = try build_unify_1(&ast);

    var ast_arena = std.heap.ArenaAllocator.init(gpa.allocator());
    var ast_builder = ASTBuilder.init(ast_arena.allocator(), &ast);

    const unify_2_index = try build_unify_2(&ast_builder);
    ast_builder.deinit();
    ast_arena.deinit();

    stdout.print("unify2: ", .{}) catch {};
    Ast.format_ast_node(stdout, unify_2_index, &ast) catch {};
    stdout.print("\n", .{}) catch {};
    try bw.flush();

    //try walk_decl(unify_1_index, &ast, &scope_env, &ty_builder, &env, &constraints);
    try walk_decl(unify_2_index, &ast, &scope_env, &ty_builder, &env, &constraints);

    stdout.print("ast: ", .{}) catch {};
    Ast.format_ast_node(stdout, unify_1_index, &ast) catch {};
    stdout.print("\n", .{}) catch {};
    try bw.flush();

    var result = try solver.solve(constraints, &env.core_env);

    try drop_temps(&result.inferences, &env);
    defer result.deinit();

    try format_result(stdout, &result, &env, &ast);
    try stdout.print("\n", .{});

    try bw.flush(); // don't forget to flush!
}

test "some test" {
    try main();
}
