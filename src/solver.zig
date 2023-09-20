const std = @import("std");
const core = @import("core.zig");

// four types of "types":
// - set (exact). These are given by declarations. They contain a list of properties (types) that they conform to.
// - inference. These accept substitutions when equated to other types.
// - Weak set. When equated to a type, this type must "contain" all of the weak set's properties, but it can contain more.
// The reported error is chosen so the "closest" matching equation is reported. This is the equation that had the highest expansions / errors rate.
// - error. These propagate no matter the direction, and contain the index of the error that was reported. This way minimal errors are reported and they appear
// on the surface, instead of appearing deep into the evaluation.
//
// Operations:
// equal (==). An inference accepts a substitution. Two bound types are equal if their list of properties are exactly equal.
// some (~). LHS must contain all of the properties of RHS.
//
//
// A constraint system is expected to be used with the solver. The constraint system will map inferences and bounded values to the notions of its type system,
// and will be able to transform the errors back into language concepts.
// Ideas:
// - member lookups are properties. An equation might map the member lookup to the type of the member on a specific struct.
// - Generic types are sets. Properties are added to them
// - A trait is a weak set. Types must implement them, but they can have more things.
// - structs are sets of their member types and method lookups.
//      A method lookup on a given struct will directly map to a method type, which might be another set.

// TODO: add "almost equal (~)" to include "following traits" (which will be just more bound ids)
// TODO: make errors for (~) include the initial source and the final erroring part.
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
