// Named type environment.
// Maps bound IDs and inference IDs to something more tangible

const std = @import("std");
const core = @import("core.zig");
const Ast = @import("ast.zig");

const log = std.log.scoped(.named);

const Ty = core.Ty;

// TODO: named Env has tight coupling with AST. Should be more decoupled, or joined
// with AST.
pub const Env = struct {
    core_env: core.Env = .{},
    inferences: std.ArrayListUnmanaged(Inference) = .{},
    variables: std.ArrayListUnmanaged(Variable) = .{},
    bound_names: std.ArrayListUnmanaged([]const u8) = .{},
    alloc: std.mem.Allocator,

    const Inference = struct {
        pub const Tag = enum(u2) {
            variable,
            typevar,
            unknown_expr,
            expr,
        };

        tag: Tag,
        index: u16,
    };

    const Variable = []const u8;

    pub fn init(alloc: std.mem.Allocator) Env {
        return .{ .alloc = alloc };
    }

    pub fn deinit(self: *Env) void {
        self.core_env.deinit(self.alloc);
        self.inferences.deinit(self.alloc);
        self.variables.deinit(self.alloc);
        self.bound_names.deinit(self.alloc);
    }

    pub fn addBoundId(self: *Env, name: []const u8) !u16 {
        const len = @as(u16, @truncate(self.bound_names.items.len));
        try self.bound_names.append(self.alloc, name);
        return len;
    }

    pub fn inference(self: *Env, inf: Inference) !u16 {
        const len = @as(u16, @truncate(self.inferences.items.len));
        try self.inferences.append(self.alloc, inf);
        return len;
    }

    pub fn unknown(self: *Env, index: u16) !u16 {
        return try self.inference(.{ .tag = .unknown_expr, .index = index });
    }

    pub fn createVar(self: *Env, comptime tag: Inference.Tag, name: Variable) !Inference {
        const var_index = @as(u16, @truncate(self.variables.items.len));
        try self.variables.append(self.alloc, name);
        return .{ .tag = tag, .index = var_index };
    }

    pub fn expr(self: *Env, expr_index: u16) !u16 {
        return try self.inference(.{ .tag = .expr, .index = expr_index });
    }

    pub fn variable(self: *Env, comptime tag: Inference.Tag, desc: Variable) !u16 {
        const i = try self.createVar(tag, desc);
        return try self.inference(i);
    }

    // create inferences for each variable. Maybe have some hint of them being
    // inferences for a (numbered) instance?
    pub fn instantiate(self: *Env, ty: Ty) !Ty {
        const Task = union(enum(u1)) { bind: struct { id: u16, count: u8 }, instantiate: Ty };

        var arena = std.heap.ArenaAllocator.init(self.alloc);
        defer arena.deinit();

        var tasks = std.ArrayList(Task).init(arena.allocator());
        defer {
            tasks.deinit();
        }

        var inference_map = std.AutoHashMap(u16, u16).init(arena.allocator());
        defer inference_map.deinit();

        var results = std.ArrayList(Ty).init(arena.allocator());
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
                            tasks.appendAssumeCapacity(.{ .bind = .{ .id = bound.id, .count = @as(u8, @truncate(bound.range.len())) } });
                            for (self.core_env.tys.items[bound.range.start..bound.range.end]) |child_ty| {
                                tasks.appendAssumeCapacity(.{ .instantiate = child_ty });
                            }
                        },
                    }
                },
                .bind => |info| {
                    try self.core_env.tys.ensureUnusedCapacity(self.alloc, info.count);
                    const start = @as(u16, @truncate(self.core_env.tys.items.len));

                    // since the results are produced into the stack in reverse order, popping them again
                    // already restores the order.
                    var i: u8 = 0;
                    while (i != info.count) : (i += 1) {
                        self.core_env.tys.appendAssumeCapacity(results.pop());
                    }

                    const end = @as(u16, @truncate(self.core_env.tys.items.len));
                    try results.append(.{ .bound = .{ .id = info.id, .range = .{ .start = start, .end = end } } });
                },
            }
        }

        return results.items[0];
    }

    pub fn formatTy(env: *const Env, ty: core.Ty, ast: *const Ast.AST) TyFmt {
        return .{ .env = env, .cached_nodefmt = ast.formatNode(0), .ty = ty };
    }

    pub const TyFmt = struct {
        env: *const Env,
        /// dummy NodeFmt to avoid reslicing the AST.
        cached_nodefmt: Ast.AST.NodeFmt,
        ty: core.Ty,

        pub fn cachedFmt(f: TyFmt, ty: core.Ty) TyFmt {
            var other = f;
            other.ty = ty;
            return other;
        }

        pub fn format(
            f: TyFmt,
            comptime _: []const u8,
            _: std.fmt.FormatOptions,
            w: anytype,
        ) @TypeOf(w).Error!void {
            switch (f.ty) {
                .inference => |id| {
                    const inference_ = f.env.inferences.items[id];
                    switch (inference_.tag) {
                        .variable => {
                            const variable_ = f.env.variables.items[inference_.index];
                            return std.fmt.format(w, "{s}", .{variable_});
                        },
                        .typevar => {
                            const variable_ = f.env.variables.items[inference_.index];
                            return std.fmt.format(w, "@{s}", .{variable_});
                        },
                        .unknown_expr => return std.fmt.format(w, "t{}", .{inference_.index}),
                        .expr => return std.fmt.format(
                            w,
                            "{}",
                            .{f.cached_nodefmt.cachedFmt(inference_.index)},
                        ),
                    }
                },
                .bound => |bound| {
                    const name = f.env.bound_names.items[bound.id];
                    if (std.mem.eql(u8, "(->)", name)) {
                        const lhs = f.env.core_env.tys.items[bound.range.start];
                        const rhs = f.env.core_env.tys.items[bound.range.start + 1];

                        const lhs_is_func =
                            lhs == .bound and std.mem.eql(
                            u8,
                            f.env.bound_names.items[lhs.bound.id],
                            "(->)",
                        );

                        if (lhs_is_func) {
                            return std.fmt.format(w, "({}) -> {}", .{
                                f.cachedFmt(lhs),
                                f.cachedFmt(rhs),
                            });
                        } else {
                            return std.fmt.format(w, "{} -> {}", .{
                                f.cachedFmt(lhs),
                                f.cachedFmt(rhs),
                            });
                        }
                    } else {
                        try std.fmt.format(w, "{s}", .{f.env.bound_names.items[bound.id]});
                        for (f.env.core_env.view(bound.range)) |child_ty| {
                            if (child_ty.hasBoundArgs()) {
                                try std.fmt.format(w, " ({})", .{f.cachedFmt(child_ty)});
                            } else {
                                try std.fmt.format(w, " {}", .{f.cachedFmt(child_ty)});
                            }
                        }
                    }
                },
            }
        }
    };
};
