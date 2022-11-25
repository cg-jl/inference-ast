const std = @import("std");

const WorldRange = struct {
    start: u16,
    end: u16,

    pub fn is_empty(self: WorldRange) bool {
        return self.start >= self.end;
    }

    pub fn len(self: WorldRange) u16 {
        return self.end - self.start;
    }

    pub fn empty() WorldRange {
        return .{ .start = 0, .end = 0 };
    }
};

const Ty = union(enum(u1)) {
    inference: u16,
    bound: struct {
        id: u16,
        range: WorldRange,
    },

    pub fn has_bound_args(self: Ty) bool {
        return switch (self) {
            .bound => |bound| !bound.range.is_empty(),
            else => false,
        };
    }
};

const CoreEnv = struct {
    // only some types require to be stored, in order to reference them
    // when looping through a bound type.
    tys: std.ArrayList(Ty),

    pub fn init(alloc: std.mem.Allocator) CoreEnv {
        return .{ .tys = std.ArrayList(Ty).init(alloc) };
    }

    pub fn deinit(self: *CoreEnv) void {
        self.tys.deinit();
    }

    pub fn clone(self: *CoreEnv, ty: Ty) !Ty {
        switch (ty) {
            // inferences can be copied just fine.
            .inference => |id| return .{ .inference = id },
            // but these ones... we have to create copies of them.
            .bound => |bound| {
                try self.tys.ensureUnusedCapacity(bound.range.len());
                const start = @truncate(u16, self.tys.items.len);

                var i = bound.range.start;
                while (i != bound.range.end) : (i += 1) {
                    const child_ty = try self.clone(self.tys.items[i]);
                    self.tys.appendAssumeCapacity(child_ty);
                }
                const end = @truncate(u16, self.tys.items.len);

                return .{ .bound = .{ .id = bound.id, .range = .{ .start = start, .end = end } } };
            },
        }
    }

    pub fn insert_ty(self: *CoreEnv, ty: Ty) !u16 {
        const id = self.tys.items.len;
        try self.tys.append(ty);
        return @truncate(u16, id);
    }
};

const Equation = struct {
    lhs: Ty,
    rhs: Ty,
};

// TODO: consider array hash map: https://devlog.hexops.com/2022/zig-hashmaps-explained/
const InferenceMap = std.AutoHashMap(u16, Ty);

fn drop_temps(inferences: *InferenceMap, env: *const NamedEnv) !void {
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

const InferenceResult = struct {
    errors: std.ArrayList(InferenceError),
    inferences: InferenceMap,

    pub fn deinit(self: *InferenceResult) void {
        self.errors.deinit();
        self.inferences.deinit();
    }
};

fn solve(constraints: std.ArrayList(Equation), env: *CoreEnv) !InferenceResult {
    var equations = constraints;
    defer equations.deinit();

    var inferences = InferenceMap.init(constraints.allocator);
    var errors = std.ArrayList(InferenceError).init(constraints.allocator);
    errdefer errors.deinit();

    while (equations.popOrNull()) |eq| {
        switch (eq.lhs) {
            .bound => |lhs_bound| switch (eq.rhs) {
                .bound => |rhs_bound| {
                    if (lhs_bound.id != rhs_bound.id) {
                        try errors.append(.{ .unsolvable_equation = eq });
                    } else {
                        // NOTE: currently this assumes that bounds have the
                        // same applied argumnets. For arbitrary arguments some
                        // modifications are needed.
                        try equations.ensureUnusedCapacity(lhs_bound.range.len());
                        var i: u16 = 0;
                        while (i != lhs_bound.range.len()) : (i += 1) {
                            equations.appendAssumeCapacity(.{
                                .lhs = env.tys.items[lhs_bound.range.start + i],
                                .rhs = env.tys.items[rhs_bound.range.start + i],
                            });
                        }
                    }
                },
                .inference => |inf| if (occurs(inf, eq.lhs, env)) {
                    try errors.append(.{ .cyclic_type = eq.lhs });
                } else {
                    substitute(inf, eq.lhs, env);

                    try inferences.put(inf, eq.lhs);
                },
            },
            .inference => |inf| if (occurs(inf, eq.rhs, env)) {
                try errors.append(.{ .cyclic_type = eq.rhs });
            } else {
                // if we're overwriting something, make sure it's equal!
                if (try inferences.fetchPut(inf, eq.rhs)) |kv| {
                    try equations.append(.{ .lhs = kv.value, .rhs = eq.rhs });
                }

                {
                    var it = inferences.iterator();
                    while (it.next()) |kv| {
                        switch (kv.value_ptr.*) {
                            .inference => |r| if (r == inf) {
                                kv.value_ptr.* = eq.rhs;
                            },
                            else => {},
                        }
                    }
                }

                substitute(inf, eq.rhs, env);
            },
        }
    }

    return .{ .inferences = inferences, .errors = errors };
}

const InferenceError = union(enum(u1)) {
    cyclic_type: Ty,
    unsolvable_equation: Equation,
};

fn occurs(inference: u16, ty: Ty, env: *const CoreEnv) bool {
    return switch (ty) {
        .inference => |id| {
            return id == inference;
        },
        .bound => |bound| {
            var i = bound.range.start;
            while (i != bound.range.end) : (i += 1) {
                if (occurs(inference, env.tys.items[i], env)) return true;
            }
            return false;
        },
    };
}

fn format_core_ty(writer: anytype, ty: Ty, env: *const CoreEnv) !void {
    switch (ty) {
        .inference => |id| {
            try std.fmt.format(writer, "'{}", .{id});
        },
        .bound => |bound| {
            try std.fmt.format(writer, "#{}", .{bound.id});
            if (!bound.range.is_empty()) {
                _ = try writer.write("<");
                try format_core_ty(writer, env.tys.items[bound.range.start], env);
                for (env.tys.items[bound.range.start + 1 .. bound.range.end]) |child| {
                    _ = try writer.write(", ");
                    try format_core_ty(writer, child, env);
                }
                _ = try writer.write(">");
            }
        },
    }
}

fn types_eq(a: Ty, b: Ty, env: *const CoreEnv) bool {
    return switch (a) {
        .inference => |id_a| switch (b) {
            .inference => |id_b| id_a == id_b,
            else => false,
        },
        .bound => |bound_a| switch (b) {
            .bound => |bound_b| {
                if (bound_b.id != bound_a.id) return false;

                if (bound_a.range.len() != bound_b.range.len()) return false;

                var i: u16 = 0;
                return while (i != bound_a.range.len()) : (i += 1) {
                    if (!types_eq(env.tys.items[bound_a.range.start + i], env.tys.items[bound_b.range.start + i], env)) break false;
                } else true;
            },
            else => false,
        },
    };
}

fn substitute(inference: u16, target: Ty, env: *CoreEnv) void {
    for (env.tys.items) |*ty| {
        switch (ty.*) {
            .inference => |r| if (r == inference) {
                ty.* = target;
            },
            else => {},
        }
    }
}

// named env
const NamedEnv = struct {
    core_env: CoreEnv,
    inferences: std.ArrayList(Inference),
    variables: std.ArrayList(Variable),
    bound_names: std.ArrayList([]const u8),

    const Inference = struct {
        pub const Tag = enum(u2) { variable, typevar, unknown_expr, expr };

        tag: Tag,
        index: u16,
    };

    const Variable = []const u8;

    pub fn init(alloc: std.mem.Allocator) NamedEnv {
        return .{ .core_env = CoreEnv.init(alloc), .inferences = std.ArrayList(Inference).init(alloc), .variables = std.ArrayList(Variable).init(alloc), .bound_names = std.ArrayList([]const u8).init(alloc) };
    }

    pub fn deinit(self: *NamedEnv) void {
        self.core_env.deinit();
        self.inferences.deinit();
        self.variables.deinit();
        self.bound_names.deinit();
    }

    pub fn add_bound_id(self: *NamedEnv, name: []const u8) !u14 {
        const len = @truncate(u14, self.bound_names.items.len);
        try self.bound_names.append(name);
        return len;
    }

    pub fn inference(self: *NamedEnv, i: Inference) !u16 {
        const len = @truncate(u16, self.inferences.items.len);
        try self.inferences.append(i);
        return len;
    }

    pub fn unknown(self: *NamedEnv, index: u14) !u16 {
        return try self.inference(.{ .tag = .unknown_expr, .index = index });
    }

    pub fn create_var(self: *NamedEnv, comptime tag: Inference.Tag, name: Variable) !Inference {
        const var_index = @truncate(u14, self.variables.items.len);
        try self.variables.append(name);
        return .{ .tag = tag, .index = var_index };
    }

    pub fn expr(self: *NamedEnv, expr_index: u16) !u16 {
        return try self.inference(.{ .tag = .expr, .index = expr_index });
    }

    pub fn variable(self: *NamedEnv, comptime tag: Inference.Tag, desc: Variable) !u16 {
        const i = try self.create_var(tag, desc);
        return try self.inference(i);
    }

    // create inferences for each variable. Maybe have some hint of them being
    // inferences for a (numbered) instance?
    pub fn instantiate(self: *NamedEnv, ty: Ty) !Ty {
        const Task = union(enum(u1)) { bind: struct { id: u16, count: u8 }, instantiate: Ty };

        var arena = std.heap.ArenaAllocator.init(self.variables.allocator);
        defer arena.deinit();

        var tasks = std.ArrayList(Task).init(arena.allocator());
        defer {
            tasks.deinit();
        }

        var inference_map = std.AutoHashMap(u16, u16).init(arena.allocator());
        defer inference_map.deinit();

        var results = std.ArrayList(Ty).init(self.variables.allocator);
        defer results.deinit();

        try tasks.append(.{ .instantiate = ty });

        while (tasks.popOrNull()) |task| {
            switch (task) {
                .instantiate => |to_instantiate| {
                    switch (to_instantiate) {
                        .inference => |id| {
                            if (self.inferences.items[id].tag == .typevar) {
                                const get_or_put = try inference_map.getOrPut(id);
                                const inf = if (!get_or_put.found_existing) putnew: {
                                    // copy the inference, but make it another ID.
                                    const name = self.variables.items[self.inferences.items[id].index];
                                    const new_inference = try self.variable(.typevar, name);
                                    get_or_put.value_ptr.* = new_inference;
                                    break :putnew new_inference;
                                } else get_or_put.value_ptr.*;
                                try results.append(.{ .inference = inf });
                            } else {
                                // leave it alone, since it's not a typevar.
                                try results.append(to_instantiate);
                            }
                        },
                        .bound => |bound| {
                            // + 1 for the extra bind task that we push to the stack
                            try tasks.ensureUnusedCapacity(bound.range.len() + 1);
                            tasks.appendAssumeCapacity(.{ .bind = .{ .id = bound.id, .count = @truncate(u8, bound.range.len()) } });
                            for (self.core_env.tys.items[bound.range.start..bound.range.end]) |child_ty| {
                                tasks.appendAssumeCapacity(.{ .instantiate = child_ty });
                            }
                        },
                    }
                },
                .bind => |info| {
                    try self.core_env.tys.ensureUnusedCapacity(info.count);
                    const start = @truncate(u16, self.core_env.tys.items.len);

                    // since the results are produced into the stack in reverse order, popping them again
                    // already restores the order.
                    var i: u8 = 0;
                    while (i != info.count) : (i += 1) {
                        self.core_env.tys.appendAssumeCapacity(results.pop());
                    }

                    const end = @truncate(u16, self.core_env.tys.items.len);
                    try results.append(.{ .bound = .{ .id = info.id, .range = .{ .start = start, .end = end } } });
                },
            }
        }

        //        std.debug.assert(results.items.len == 1, "must have consumed all the result stack but one");
        return results.items[0];
    }
};

// AST

const DeclInfo = struct {
    name_index: u16,
    // the patterns are directly adjacent to the node.
    arg_count: u8, // NOTE: here we're supporting up to 256 arguments + 256 clauses PER declaration. We can surely shorten this.
    // the clauses are directly to the left of the arguments.
    clause_count: u8,
    expr_id: u16,
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

    pub fn as_ref(self: NodeData) u16 {
        return self.lhs;
    }

    pub fn equals(self: NodeData, other: NodeData) bool {
        return self.lhs == other.lhs and self.rhs == other.rhs;
    }

    const Decl = struct { name: []const u8, args_begin: u16, args_end: u16, clauses_begin: u16, clauses_end: u16, expr: u16 };

    pub fn as_bind(self: NodeData, ast: *const AST) struct { name: []const u8, expr: u16 } {
        return .{ .name = ast.as_name(self.lhs), .expr = self.rhs };
    }

    pub fn as_apply(self: NodeData) struct { func: u16, arg: u16 } {
        return .{ .func = self.lhs, .arg = self.rhs };
    }

    pub fn as_decl(self: NodeData, index: u16, ast: *const AST) Decl {
        const decl_info = ast.decl_infos.items[self.lhs];
        return .{ .name = ast.as_name(decl_info.name_index), .args_begin = index - decl_info.arg_count, .args_end = index, .clauses_begin = index - decl_info.arg_count - decl_info.clause_count, .clauses_end = index - decl_info.arg_count, .expr = decl_info.expr_id };
    }

    pub fn as_if(self: NodeData, index: u16, ast: *const AST) struct { condition: u16, then_part: u16, else_part: u16 } {
        const info = ast.ifs.items[self.rhs];
        return .{ .condition = self.lhs, .then_part = index - info.then_distance, .else_part = index - info.else_distance };
    }
};

const IfData = struct {
    then_distance: u8,
    else_distance: u8,
};

const AST = struct {
    // NOTE: decl_infos, names and ifs could be all merged together.
    decl_infos: std.ArrayList(DeclInfo),

    nodes: std.MultiArrayList(Node),
    names: std.ArrayList([]const u8),

    ifs: std.ArrayList(IfData),
    alloc: std.mem.Allocator,

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

    pub inline fn as_name(self: *const AST, name_index: u16) []const u8 {
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
        const idx = @truncate(u16, self.nodes.len);

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
        const res = @truncate(u16, self.nodes.len);
        const if_index = @truncate(u16, self.ifs.items.len);
        self.ifs.appendAssumeCapacity(.{
            .then_distance = @truncate(u8, res - then_part),
            .else_distance = @truncate(u8, res - else_part),
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

        const decl_info_index = @truncate(u16, self.decl_infos.items.len);
        // now add the decl info
        self.decl_infos.appendAssumeCapacity(.{ .name_index = name_index, .arg_count = @truncate(u8, args.len), .clause_count = @truncate(u8, clauses.len), .expr_id = res });

        return self.pushNodeAssumeCapacity(.{ .tag = .decl, .data = .{
            .lhs = decl_info_index,
            .rhs = 0,
        } });
    }
};

fn format_ty(writer: anytype, ty: Ty, env: *const NamedEnv, ast: *const AST) !void {
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
                    try format_ast_node(writer, inference.index, ast);
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
                    try format_ty(writer, env.core_env.tys.items[bound.range.start], env, ast);
                    _ = try writer.write(")");
                } else {
                    try format_ty(writer, env.core_env.tys.items[bound.range.start], env, ast);
                }

                _ = try writer.write(" -> ");
                try format_ty(writer, env.core_env.tys.items[bound.range.start + 1], env, ast);
            } else {
                try std.fmt.format(writer, "{s}", .{env.bound_names.items[bound.id]});
                for (env.core_env.tys.items[bound.range.start..bound.range.end]) |child_ty| {
                    _ = try writer.write(" ");

                    if (child_ty.has_bound_args()) {
                        _ = try writer.write("(");
                        try format_ty(writer, child_ty, env, ast);
                        _ = try writer.write(")");
                    } else {
                        try format_ty(writer, child_ty, env, ast);
                    }
                }
            }
        },
    }
}

fn format_inferences(writer: anytype, inferences: *const InferenceMap, env: *const NamedEnv, ast: *const AST) !void {
    _ = try writer.write("inferences:\n");
    var it = inferences.iterator();
    while (it.next()) |entry| {
        try format_ty(writer, .{ .inference = entry.key_ptr.* }, env, ast);
        _ = try writer.write(" :: ");
        try format_ty(writer, entry.value_ptr.*, env, ast);
        _ = try writer.write("\n");
    }
}

fn format_error(writer: anytype, err: InferenceError, env: *const NamedEnv, ast: *const AST) !void {
    switch (err) {
        .cyclic_type => |ty| {
            _ = try writer.write("cyclic type: ");
            try format_ty(writer, ty, env, ast);
        },
        .unsolvable_equation => |eq| {
            _ = try writer.write("Cannot equate ");
            try format_ty(writer, eq.lhs, env, ast);
            _ = try writer.write(" to ");
            try format_ty(writer, eq.rhs, env, ast);
        },
    }
}

fn format_result(writer: anytype, results: *const InferenceResult, env: *const NamedEnv, ast: *const AST) !void {
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

    pub fn bound_id(self: *Self, name: []const u8, env: *NamedEnv) !u16 {
        const get_or_put = try self.bounds.getOrPut(self.alloc, name);
        if (!get_or_put.found_existing) {
            get_or_put.value_ptr.* = try env.add_bound_id(name);
        }
        return get_or_put.value_ptr.*;
    }

    pub fn type_var(self: *Self, name: []const u8, env: *NamedEnv) !u16 {
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
    pub fn format_hintmap(self: *const Self, w: anytype, ast: *const AST, env: *const NamedEnv) void {
        std.fmt.format(w, "hints in current scope:\n", .{}) catch {};
        var iter = self.scopes.items[self.current_scope].hints.iterator();
        while (iter.next()) |i| {
            std.fmt.format(w, "{s} = ", .{i.key_ptr.*}) catch {};
            format_ty(w, i.value_ptr.*, env, ast) catch {};
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

        pub fn define(self: *Scope, name: []const u8, env: *NamedEnv, alloc: std.mem.Allocator) !u16 {
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
    pub fn unknown(self: *Self, env: *NamedEnv) !u16 {
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

    pub fn get(self: *Self, name: []const u8, env: *NamedEnv) !Ty {
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
                        break h: {
                            break :h h;
                        };
                    if (self.scopes.items[current_scope].parent) |p| {
                        current_scope = p;
                    } else break null;
                };
            };

            break :instantiate_unknown if (found_hint) |hint| try env.instantiate(hint) else Ty{ .inference = try env.variable(.variable, name) };
        };

        return final_inference;
    }

    pub fn define(self: *Self, name: []const u8, env: *NamedEnv) !u16 {
        return try self.scopes.items[self.current_scope].define(name, env, self.arena.allocator());
    }
};

fn apply(a: Ty, b: Ty, res: Ty, types: *TypeBuilder, env: *NamedEnv) !Equation {
    try env.core_env.tys.ensureUnusedCapacity(2);
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

fn walk_expr(index: u16, ast: *const AST, scope_env: *ScopeEnv, types: *TypeBuilder, env: *NamedEnv, equations: *std.ArrayList(Equation)) !Ty {
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
            const bool_ty = .{ .bound = .{ .id = try types.bound_id("Bool", env), .range = WorldRange.empty() } };
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
fn walk_pattern(index: u16, ast: *const AST, scope_env: *ScopeEnv, types: *TypeBuilder, env: *NamedEnv, equations: *std.ArrayList(Equation)) !Ty {
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

fn walk_decl(index: u16, ast: *AST, scope_env: *ScopeEnv, types: *TypeBuilder, env: *NamedEnv, equations: *std.ArrayList(Equation)) !void {
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

fn format_constraints(writer: anytype, constraints: []const Equation, env: *const NamedEnv, ast: *const AST) !void {
    for (constraints) |c| {
        try format_ty(writer, c.lhs, env, ast);
        _ = try writer.write(" = ");
        try format_ty(writer, c.rhs, env, ast);
        _ = try writer.write("\n");
    }
}

fn format_ast_node(writer: anytype, index: u16, ast: *const AST) !void {
    switch (ast.nodes.items(.tag)[index]) {
        .decl => {
            const info = ast.nodes.items(.data)[index].as_decl(index, ast);
            _ = try writer.write(info.name);
            _ = try writer.write(" ");
            {
                var current_arg = info.args_begin;
                while (current_arg != info.args_end) : (current_arg += 1) {
                    if (ast.nodes.items(.tag)[current_arg] == .apply) {
                        _ = try writer.write("(");
                        try format_ast_node(writer, current_arg, ast);
                        _ = try writer.write(")");
                    } else {
                        try format_ast_node(writer, current_arg, ast);
                    }
                    _ = try writer.write(" ");
                }
            }

            _ = try writer.write(" = ");
            try format_ast_node(writer, info.expr, ast);

            if (info.clauses_begin != info.args_begin) {
                _ = try writer.write("\n    where ");
                try format_ast_node(writer, info.clauses_begin, ast);
                var current_clause = info.clauses_begin + 1;
                while (current_clause != info.args_begin) : (current_clause += 1) {
                    _ = try writer.write("\n          ");
                    try format_ast_node(writer, current_clause, ast);
                }
            }
        },
        .bind => {
            const info = ast.nodes.items(.data)[index].as_bind(ast);
            _ = try writer.write(info.name);
            _ = try writer.write("@");
            if (ast.nodes.items(.tag)[info.expr] == .apply) {
                _ = try writer.write("(");
                try format_ast_node(writer, info.expr, ast);
                _ = try writer.write(")");
            } else {
                try format_ast_node(writer, info.expr, ast);
            }
        },
        .apply => {
            const info = ast.nodes.items(.data)[index].as_apply();
            try format_ast_node(writer, info.func, ast);
            _ = try writer.write(" ");
            if (ast.nodes.items(.tag)[info.arg] == .apply) {
                _ = try writer.write("(");
                try format_ast_node(writer, info.arg, ast);
                _ = try writer.write(")");
            } else {
                try format_ast_node(writer, info.arg, ast);
            }
        },
        .name_lookup => {
            const name_index = ast.nodes.items(.data)[index].as_ref();
            const name = ast.as_name(name_index);
            _ = try writer.write(name);
        },
        .ignored => {
            _ = try writer.write("_");
        },
        .ifexpr => {
            const info = ast.nodes.items(.data)[index].as_if(index, ast);
            _ = try writer.write("if ");
            try format_ast_node(writer, info.condition, ast);
            _ = try writer.write(" then ");
            try format_ast_node(writer, info.then_part, ast);
            _ = try writer.write(" else ");
            try format_ast_node(writer, info.else_part, ast);
        },
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

    ast: *AST,
    name_cache: std.StringHashMapUnmanaged(NameInfo),
    // the AST and the Parser have distinct allocs since the parser cache will be
    // cleaned right after we're done with parsing.
    alloc: std.mem.Allocator,

    pub fn init(alloc: std.mem.Allocator, ast: *AST) Self {
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
    const arg0 = AST.Node.apply(inference_lookup.lookup_node, a.lookup_node);
    const arg1 = AST.Node.lookup(k.name_index);

    return try builder.ast.decl(unify.name_index, &.{ arg0, arg1 }, res, &.{});
}

fn build_unify_1(ast: *AST) !u16 {

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

    var env = NamedEnv.init(arena.allocator());
    defer env.deinit();

    var ast = AST.init(arena.allocator());
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
        const bool_ty = Ty{ .bound = .{ .id = try ty_builder.bound_id("Bool", &env), .range = WorldRange.empty() } };
        const func_bound_id = try ty_builder.bound_id("(->)", &env);

        const unify_event_a = build_unify_ev: {
            const start = try env.core_env.insert_ty(a_typevar);
            break :build_unify_ev Ty{ .bound = .{
                .id = try ty_builder.bound_id("UnifyEvent", &env),
                .range = .{ .start = start, .end = start + 1 },
            } };
        };

        const unify_error_a = build_unify_err: {
            const start = try env.core_env.insert_ty(a_typevar);
            break :build_unify_err Ty{ .bound = .{ .id = try ty_builder.bound_id("UnifyError", &env), .range = .{ .start = start, .end = start + 1 } } };
        };

        const either_e_a = build_either: {
            const bound_id = try ty_builder.bound_id("Either", &env);
            const start = try env.core_env.insert_ty(e_typevar);
            _ = try env.core_env.insert_ty(a_typevar);
            break :build_either Ty{ .bound = .{
                .id = bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        };

        //        try scope_env.add_hint("Empty", unify_event_a);

        try scope_env.add_hint("Right", mkRight: {
            const start = try env.core_env.insert_ty(a_typevar);
            _ = try env.core_env.insert_ty(either_e_a);
            break :mkRight .{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        });

        try scope_env.add_hint("Left", mkLeft: {
            const start = try env.core_env.insert_ty(e_typevar);
            _ = try env.core_env.insert_ty(either_e_a);
            break :mkLeft .{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        });

        //const list_bound_id = try ty_builder.bound_id("[]", &env);

        {
            const a2bool = a2bool: {
                const start = try env.core_env.insert_ty(a_typevar);
                _ = try env.core_env.insert_ty(bool_ty);
                break :a2bool Ty{ .bound = .{ .id = func_bound_id, .range = .{ .start = start, .end = start + 2 } } };
            };

            const eq = eq: {
                const start = try env.core_env.insert_ty(a_typevar);
                _ = try env.core_env.insert_ty(a2bool);
                break :eq Ty{ .bound = .{ .id = func_bound_id, .range = .{ .start = start, .end = start + 2 } } };
            };

            try scope_env.add_hint("(==)", eq);
        }

        const inference_ty_id = try ty_builder.bound_id("InferenceTy", &env);

        const inference_ty_a = inference_ty: {
            const start = try env.core_env.insert_ty(a_typevar);
            break :inference_ty Ty{ .bound = .{
                .id = inference_ty_id,
                .range = .{ .start = start, .end = start + 1 },
            } };
        };
        try scope_env.add_hint("CyclicType", mkCT: {
            const start = try env.core_env.insert_ty(inference_ty_a);
            _ = try env.core_env.insert_ty(unify_error_a);
            break :mkCT .{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        });

        try scope_env.add_hint("Infer", build_infer: {
            // InferenceTy a -> UnifyEvent a
            const middle_param = try env.core_env.insert_ty(inference_ty_a);
            _ = try env.core_env.insert_ty(unify_event_a);

            // a -> (InferenceTy a -> UnifyEvent a)
            const start = try env.core_env.insert_ty(a_typevar);
            _ = try env.core_env.insert_ty(.{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = middle_param, .end = middle_param + 2 },
            } });
            break :build_infer Ty{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        });

        try scope_env.add_hint("Inference", inference: {
            const start = try env.core_env.insert_ty(a_typevar);
            _ = try env.core_env.insert_ty(inference_ty_a);
            break :inference .{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        });

        //        const list_of_inference_ty_a = mklist: {
        //            const start = try env.core_env.insert_ty(inference_ty_a);
        //            break :mklist Ty{ .bound = .{ .bound_id = list_bound_id, .bound_range = .{ .start = start, .end = start + 1 } } };
        //        };
        //
        //        try scope_env.add_hint("Bound", mkBound: {
        //            const func_list_to_a = mkList2a: {
        //                const start = try env.core_env.insert_ty(list_of_inference_ty_a);
        //                _ = try env.core_env.insert_ty(inference_ty_a);
        //                break :mkList2a Ty{ .bound = .{
        //                    .bound_id = func_bound_id,
        //                    .bound_range = .{ .start = start, .end = start + 2 },
        //                } };
        //            };
        //
        //            const start = try env.core_env.insert_ty(a_typevar);
        //            _ = try env.core_env.insert_ty(func_list_to_a);
        //            break :mkBound .{ .bound = .{
        //                .bound_id = func_bound_id,
        //                .bound_range = .{ .start = start, .end = start + 2 },
        //            } };
        //        });
    }

    scope_env.format_hintmap(stdout, &ast, &env);

    // constraints also go into GPA since its allocations are sporadic.
    var constraints = std.ArrayList(Equation).init(gpa.allocator());

    const unify_1_index = try build_unify_1(&ast);

    var ast_arena = std.heap.ArenaAllocator.init(gpa.allocator());
    var ast_builder = ASTBuilder.init(ast_arena.allocator(), &ast);

    const unify_2_index = try build_unify_2(&ast_builder);
    ast_builder.deinit();
    ast_arena.deinit();

    stdout.print("unify2: ", .{}) catch {};
    format_ast_node(stdout, unify_2_index, &ast) catch {};
    stdout.print("\n", .{}) catch {};
    try bw.flush();

    //try walk_decl(unify_1_index, &ast, &scope_env, &ty_builder, &env, &constraints);
    try walk_decl(unify_2_index, &ast, &scope_env, &ty_builder, &env, &constraints);


    stdout.print("ast: ", .{}) catch {};
    format_ast_node(stdout, unify_1_index, &ast) catch {};
    stdout.print("\n", .{}) catch {};
    try bw.flush();

    var result = try solve(constraints, &env.core_env);

    try drop_temps(&result.inferences, &env);
    defer result.deinit();

    try format_result(stdout, &result, &env, &ast);
    try stdout.print("\n", .{});

    try bw.flush(); // don't forget to flush!
}

test "simple test" {
    var list = std.ArrayList(i32).init(std.testing.allocator);
    defer list.deinit(); // try commenting this out and see if zig detects the memory leak!
    try list.append(42);
    try std.testing.expectEqual(@as(i32, 42), list.pop());
}
