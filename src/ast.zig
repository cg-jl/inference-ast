const std = @import("std");
const named = @import("named.zig");
const core = @import("core.zig");

pub const Builder = struct {
    const Self = @This();

    pub const NameInfo = struct { lookup_node: u16, name_index: u16 };

    ast: *AST,
    name_cache: std.StringHashMapUnmanaged(NameInfo),
    // the Ast.AST and the Parser have distinct allocs since the parser cache will be
    // cleaned right after we're done with parsing.
    alloc: std.mem.Allocator,

    pub fn init(alloc: std.mem.Allocator, ast: *AST) Self {
        return .{ .ast = ast, .name_cache = .{}, .alloc = alloc };
    }

    pub fn cachedNameAssumeCapacity(self: *Self, name: []const u8) NameInfo {
        const get_or_put = self.lookup_node_cache.getOrPutAssumeCapacity(name);
        if (!get_or_put.found_existing) {
            const index = @as(u16, @truncate(self.ast.names.len));
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
            const index = @as(u16, @truncate(self.ast.names.items.len));
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
const NodeKind = enum(u4) {
    // lhs: declaration info index
    decl,
    // lhs: index to string table
    // rhs: index to expr.
    bind,
    // lhs: index to function expr
    // rhs: index to arg expr
    apply,
    // lhs: index to string table
    name_lookup,
    // nothing.
    ignored,
    // lhs: condition
    // rhs: then & else in extra data
    ifexpr,
};

const NodeData = struct {
    lhs: u16,
    rhs: u16,

    pub fn asRef(self: NodeData) u16 {
        return self.lhs;
    }

    pub fn equals(self: NodeData, other: NodeData) bool {
        return self.lhs == other.lhs and self.rhs == other.rhs;
    }

    const Decl = struct { name: []const u8, args_begin: u16, args_end: u16, clauses_begin: u16, clauses_end: u16, expr: u16 };

    pub fn asBind(self: NodeData, ast: *const AST) struct { name: []const u8, expr: u16 } {
        return .{ .name = ast.asName(self.lhs), .expr = self.rhs };
    }

    pub fn asApply(self: NodeData) struct { func: u16, arg: u16 } {
        return .{ .func = self.lhs, .arg = self.rhs };
    }

    pub fn asDecl(self: NodeData, index: u16, ast: *const AST) Decl {
        const decl_info = ast.decl_infos.items[self.lhs];
        return .{ .name = ast.asName(decl_info.name_index), .args_begin = index - decl_info.arg_count, .args_end = index, .clauses_begin = index - decl_info.arg_count - decl_info.clause_count, .clauses_end = index - decl_info.arg_count, .expr = decl_info.expr_id };
    }

    pub fn asIf(self: NodeData, index: u16, ast: *const AST) struct { condition: u16, then_part: u16, else_part: u16 } {
        const info = ast.ifs.items[self.rhs];
        return .{ .condition = self.lhs, .then_part = index - info.then_distance, .else_part = index - info.else_distance };
    }
};

const DeclInfo = struct {
    name_index: u16,
    // the patterns are directly adjacent to the node.
    arg_count: u8, // NOTE: here we're supporting up to 256 arguments + 256 clauses PER declaration. We can surely shorten this.
    // the clauses are directly to the left of the arguments.
    clause_count: u8,
    expr_id: u16,
};

const IfData = struct {
    then_distance: u8,
    else_distance: u8,
};

pub const Node = struct {
    tag: NodeKind,
    data: NodeData,

    pub inline fn apply(func: u16, arg: u16) Node {
        return .{
            .tag = .apply,
            .data = .{ .lhs = func, .rhs = arg },
        };
    }

    pub inline fn lookup(name_index: u16) Node {
        return .{
            .tag = .name_lookup,
            .data = .{ .lhs = name_index, .rhs = 0 },
        };
    }
};

pub const AST = struct {
    // NOTE: decl_infos, names and ifs could be all merged together.
    decl_infos: std.ArrayList(DeclInfo),

    nodes: std.MultiArrayList(Node),
    names: std.ArrayList([]const u8),

    ifs: std.ArrayList(IfData),
    alloc: std.mem.Allocator,

    pub fn init(alloc: std.mem.Allocator) AST {
        return .{
            .decl_infos = std.ArrayList(DeclInfo).init(alloc),
            .nodes = .{},
            .names = std.ArrayList([]const u8).init(alloc),
            .ifs = std.ArrayList(IfData).init(alloc),
            .alloc = alloc,
        };
    }

    pub fn deinit(self: *AST) void {
        self.decl_infos.deinit();
        self.nodes.deinit(self.alloc);
    }

    pub inline fn asName(self: *const AST, name_index: u16) []const u8 {
        return self.names.items[name_index];
    }

    pub inline fn apply(self: *AST, func: u16, arg: u16) !u16 {
        try self.nodes.ensureUnusedCapacity(self.alloc, 1);
        return self.applyAssumeCapacity(func, arg);
    }

    pub inline fn applyAssumeCapacity(self: *AST, func: u16, arg: u16) u16 {
        return self.pushNodeAssumeCapacity(Node.apply(func, arg));
    }

    pub inline fn pushNodeAssumeCapacity(self: *AST, node: Node) u16 {
        const idx = @as(u16, @truncate(self.nodes.len));

        self.nodes.appendAssumeCapacity(node);

        return idx;
    }

    pub inline fn pushNode(self: *AST, node: Node) !u16 {
        try self.nodes.ensureUnusedCapacity(self.alloc, 1);
        return self.pushNodeAssumeCapacity(node);
    }

    pub inline fn pushIf(self: *AST, condition: u16, then_part: u16, else_part: u16) !u16 {
        try self.ifs.ensureUnusedCapacity(1);
        try self.nodes.ensureUnusedCapacity(self.alloc, 1);
        return self.pushIfAssumeCapacity(condition, then_part, else_part);
    }

    // Pushes a new if expression, assuming there is allocated space for:
    // - a node
    // - an if data
    pub fn pushIfAssumeCapacity(self: *AST, condition: u16, then_part: u16, else_part: u16) u16 {
        const res = @as(u16, @truncate(self.nodes.len));
        const if_index = @as(u16, @truncate(self.ifs.items.len));
        self.ifs.appendAssumeCapacity(.{
            .then_distance = @as(u8, @truncate(res - then_part)),
            .else_distance = @as(u8, @truncate(res - else_part)),
        });

        return self.pushNodeAssumeCapacity(.{
            .tag = .ifexpr,
            .data = .{ .lhs = condition, .rhs = if_index },
        });
    }

    pub inline fn name(self: *AST, name_index: u16) !u16 {
        return try self.pushNode(.{
            .tag = .name_lookup,
            .data = .{ .lhs = name_index, .rhs = 0 },
        });
    }

    pub inline fn nameAssumeCapacity(self: *AST, name_index: u16) u16 {
        return self.pushNodeAssumeCapacity(.{
            .tag = .name_lookup,
            .data = .{ .lhs = name_index, .rhs = 0 },
        });
    }

    // Pushes a new declaration, ensuring firsrt that there is enough allocation space.
    pub inline fn decl(self: *AST, name_index: u16, args: []const Node, res: u16, clauses: []const Node) !u16 {
        try self.nodes.ensureUnusedCapacity(self.alloc, args.len + clauses.len + 1);
        try self.decl_infos.ensureUnusedCapacity(1);
        return self.declAssumeCapacity(name_index, args, res, clauses);
    }

    // Pushes a new declaration assuming there is allocated space for:
    // - all argument nodes that were deferred for insertion
    // - all clause nodes that were deferred for insertion
    // - the final declaration node
    // - one more space in decl_infos for the declaration information.
    pub fn declAssumeCapacity(self: *AST, name_index: u16, args: []const Node, res: u16, clauses: []const Node) u16 {
        // first, add the clauses
        for (clauses) |clause| {
            _ = self.pushNodeAssumeCapacity(clause);
        }

        // then, add the args
        for (args) |arg| {
            _ = self.pushNodeAssumeCapacity(arg);
        }

        const decl_info_index = @as(u16, @truncate(self.decl_infos.items.len));
        // now add the decl info
        self.decl_infos.appendAssumeCapacity(.{ .name_index = name_index, .arg_count = @as(u8, @truncate(args.len)), .clause_count = @as(u8, @truncate(clauses.len)), .expr_id = res });

        return self.pushNodeAssumeCapacity(.{ .tag = .decl, .data = .{
            .lhs = decl_info_index,
            .rhs = 0,
        } });
    }
};

pub fn formatTy(writer: anytype, ty: core.Ty, env: *const named.Env, ast: *const AST) !void {
    switch (ty) {
        .inference => |id| {
            const inference = env.inferences.items[id];
            switch (inference.tag) {
                .variable => {
                    const variable = env.variables.items[inference.index];
                    try std.fmt.format(writer, "{s}", .{variable});
                },
                .typevar => {
                    const variable = env.variables.items[inference.index];
                    try std.fmt.format(writer, "@{s}", .{variable});
                },
                .unknown_expr => {
                    try std.fmt.format(writer, "t{}", .{inference.index});
                },
                .expr => {
                    try formatAstNode(writer, inference.index, ast);
                },
            }
        },
        .bound => |bound| {
            if (std.mem.eql(u8, env.bound_names.items[bound.id], "(->)")) {
                const lhs_is_func = switch (env.core_env.tys.items[bound.range.start]) {
                    .bound => |bound2| std.mem.eql(u8, env.bound_names.items[bound2.id], "(->)"),
                    else => false,
                };

                if (lhs_is_func) {
                    _ = try writer.write("(");
                    try formatTy(writer, env.core_env.tys.items[bound.range.start], env, ast);
                    _ = try writer.write(")");
                } else {
                    try formatTy(writer, env.core_env.tys.items[bound.range.start], env, ast);
                }

                _ = try writer.write(" -> ");
                try formatTy(writer, env.core_env.tys.items[bound.range.start + 1], env, ast);
            } else {
                try std.fmt.format(writer, "{s}", .{env.bound_names.items[bound.id]});
                for (env.core_env.tys.items[bound.range.start..bound.range.end]) |child_ty| {
                    _ = try writer.write(" ");

                    if (child_ty.hasBoundArgs()) {
                        _ = try writer.write("(");
                        try formatTy(writer, child_ty, env, ast);
                        _ = try writer.write(")");
                    } else {
                        try formatTy(writer, child_ty, env, ast);
                    }
                }
            }
        },
    }
}

pub fn formatAstNode(writer: anytype, index: u16, ast: *const AST) !void {
    switch (ast.nodes.items(.tag)[index]) {
        .decl => {
            const info = ast.nodes.items(.data)[index].asDecl(index, ast);
            _ = try writer.write(info.name);
            _ = try writer.write(" ");
            {
                var current_arg = info.args_begin;
                while (current_arg != info.args_end) : (current_arg += 1) {
                    if (ast.nodes.items(.tag)[current_arg] == .apply) {
                        _ = try writer.write("(");
                        try formatAstNode(writer, current_arg, ast);
                        _ = try writer.write(")");
                    } else {
                        try formatAstNode(writer, current_arg, ast);
                    }
                    _ = try writer.write(" ");
                }
            }

            _ = try writer.write(" = ");
            try formatAstNode(writer, info.expr, ast);

            if (info.clauses_begin != info.args_begin) {
                _ = try writer.write("\n    where ");
                try formatAstNode(writer, info.clauses_begin, ast);
                var current_clause = info.clauses_begin + 1;
                while (current_clause != info.args_begin) : (current_clause += 1) {
                    _ = try writer.write("\n          ");
                    try formatAstNode(writer, current_clause, ast);
                }
            }
        },
        .bind => {
            const info = ast.nodes.items(.data)[index].asBind(ast);
            _ = try writer.write(info.name);
            _ = try writer.write("@");
            if (ast.nodes.items(.tag)[info.expr] == .apply) {
                _ = try writer.write("(");
                try formatAstNode(writer, info.expr, ast);
                _ = try writer.write(")");
            } else {
                try formatAstNode(writer, info.expr, ast);
            }
        },
        .apply => {
            const info = ast.nodes.items(.data)[index].asApply();
            try formatAstNode(writer, info.func, ast);
            _ = try writer.write(" ");
            if (ast.nodes.items(.tag)[info.arg] == .apply) {
                _ = try writer.write("(");
                try formatAstNode(writer, info.arg, ast);
                _ = try writer.write(")");
            } else {
                try formatAstNode(writer, info.arg, ast);
            }
        },
        .name_lookup => {
            const name_index = ast.nodes.items(.data)[index].asRef();
            const name = ast.asName(name_index);
            _ = try writer.write(name);
        },
        .ignored => {
            _ = try writer.write("_");
        },
        .ifexpr => {
            const info = ast.nodes.items(.data)[index].asIf(index, ast);
            _ = try writer.write("if ");
            try formatAstNode(writer, info.condition, ast);
            _ = try writer.write(" then ");
            try formatAstNode(writer, info.then_part, ast);
            _ = try writer.write(" else ");
            try formatAstNode(writer, info.else_part, ast);
        },
    }
}
