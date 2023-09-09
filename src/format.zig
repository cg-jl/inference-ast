const solver = @import("solver.zig");
const std = @import("std");
const named = @import("named.zig");
const Ast = @import("ast.zig");

const ConstraintFmt = struct {
    constraints: []const solver.Equation,
    cached_fmt: named.Env.TyFmt,

    pub fn format(
        c: ConstraintFmt,
        comptime _: []const u8,
        _: std.fmt.FormatOptions,
        w: anytype,
    ) @TypeOf(w).Error!void {
        for (c.constraints) |constraint| {
            try std.fmt.format(w, "{} = {}\n", .{
                c.cached_fmt.cachedFmt(constraint.lhs),
                c.cached_fmt.cachedFmt(constraint.rhs),
            });
        }
    }
};

fn formatConstraints(
    constraints: []const solver.Equation,
    env: *const named.Env,
    ast: *const Ast.AST,
) ConstraintFmt {
    return .{
        .constraints = constraints,
        .cached_fmt = env.formatTy(.{ .inference = 0 }, ast),
    };
}

fn formatInferences(writer: anytype, inferences: *const solver.Map, cached_fmt: named.Env.TyFmt) !void {
    try writer.writeAll("inferences:\n");
    var it = inferences.iterator();
    while (it.next()) |entry| {
        try writer.print("{} :: {}\n", .{
            cached_fmt.cachedFmt(.{ .inference = entry.key_ptr.* }),
            cached_fmt.cachedFmt(entry.value_ptr.*),
        });
    }
}

fn formatError(writer: anytype, err: solver.Error, cached_fmt: named.Env.TyFmt) !void {
    switch (err) {
        .cyclic_type => |ty| return writer.print("{}", .{cached_fmt.cachedFmt(ty)}),
        .unequal_bounds => |eq| {
            const lhs_fmt = cached_fmt.cachedFmt(eq.lhs);
            const rhs_fmt = cached_fmt.cachedFmt(eq.rhs);

            return writer.print("Cannot equate {} to {}", .{ lhs_fmt, rhs_fmt });
        },
    }
}

const ResultFmt = struct {
    results: *const solver.Result,
    ty_fmt: named.Env.TyFmt,
};

pub fn formatResult(writer: anytype, results: *const solver.Result, env: *const named.Env, ast: *const Ast.AST) !void {
    const cached_fmt = env.formatTy(.{ .inference = 0 }, ast);
    _ = try writer.write("errors:\n");
    for (results.errors.items) |err| {
        try formatError(writer, err, cached_fmt);
        _ = try writer.write("\n");
    }

    return formatInferences(writer, &results.inferences, cached_fmt);
}
