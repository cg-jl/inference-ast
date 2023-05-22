const std = @import("std");
const core = @import("core.zig");

pub const Equation = struct {
    lhs: core.Ty,
    rhs: core.Ty,
};

pub const Map = std.AutoHashMap(u16, core.Ty);

pub const Result = struct {
    errors: std.ArrayList(Error),
    inferences: Map,

    pub fn deinit(self: *Result) void {
        self.errors.deinit();
        self.inferences.deinit();
    }
};

pub const Error = union(enum(u1)) {
    cyclic_type: core.Ty,
    unequal_bounds: Equation,
};

pub fn solve(constraints: std.ArrayList(Equation), env: *core.Env) !Result {
    var equations = constraints;
    defer equations.deinit();

    var inferences = Map.init(constraints.allocator);
    var errors = std.ArrayList(Error).init(constraints.allocator);
    errdefer errors.deinit();
    errdefer inferences.deinit();

    while (equations.popOrNull()) |eq| {
        switch (eq.lhs) {
            .bound => |lhs_bound| switch (eq.rhs) {
                .bound => |rhs_bound| {
                    if (lhs_bound.id != rhs_bound.id) {
                        try errors.append(.{ .unequal_bounds = eq });
                    } else {
                        // NOTE: currently this assumes that bounds have the same applied arguments. For
                        // arbitrary arguments some modifications are needed.
                        try equations.ensureUnusedCapacity(lhs_bound.range.len());
                        for (env.view(lhs_bound.range), 0..) |lty, i| {
                            const rty = env.tys.items[rhs_bound.range.start + i];
                            equations.appendAssumeCapacity(.{
                                .lhs = lty,
                                .rhs = rty,
                            });
                        }
                    }
                },
                .inference => |inf| if (core.occurs(inf, eq.lhs, env)) {
                    try errors.append(.{ .cyclic_type = eq.lhs });
                } else {
                    core.substitute(inf, eq.lhs, env);
                    try inferences.put(inf, eq.lhs);
                },
            },
            .inference => |inf| if (core.occurs(inf, eq.rhs, env)) {
                try errors.append(.{ .cyclic_type = eq.rhs });
            } else {
                // if we're overwriting something, make sure it's equal!
                if (try inferences.fetchPut(inf, eq.rhs)) |kv| {
                    try equations.append(.{ .lhs = kv.value, .rhs = eq.rhs });
                }

                // substitute the inference in our inference map
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

                // substitute the inference in the env
                core.substitute(inf, eq.rhs, env);
            },
        }
    }

    return .{ .inferences = inferences, .errors = errors };
}
