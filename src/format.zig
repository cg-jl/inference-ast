const solver = @import("solver.zig");
const named = @import("named.zig");
const Ast = @import("ast.zig");

fn formatConstraints(writer: anytype, constraints: []const solver.Equation, env: *const named.Env, ast: *const Ast.AST) !void {
    for (constraints) |c| {
        try Ast.formatTy(writer, c.lhs, env, ast);
        _ = try writer.write(" = ");
        try Ast.formatTy(writer, c.rhs, env, ast);
        _ = try writer.write("\n");
    }
}
fn formatInferences(writer: anytype, inferences: *const solver.Map, env: *const named.Env, ast: *const Ast.AST) !void {
    _ = try writer.write("inferences:\n");
    var it = inferences.iterator();
    while (it.next()) |entry| {
        try Ast.formatTy(writer, .{ .inference = entry.key_ptr.* }, env, ast);
        _ = try writer.write(" :: ");
        try Ast.formatTy(writer, entry.value_ptr.*, env, ast);
        _ = try writer.write("\n");
    }
}

fn formatError(writer: anytype, err: solver.Error, env: *const named.Env, ast: *const Ast.AST) !void {
    switch (err) {
        .cyclic_type => |ty| {
            _ = try writer.write("cyclic type: ");
            try Ast.formatTy(writer, ty, env, ast);
        },
        .unequal_bounds => |eq| {
            _ = try writer.write("Cannot equate ");
            try Ast.formatTy(writer, eq.lhs, env, ast);
            _ = try writer.write(" to ");
            try Ast.formatTy(writer, eq.rhs, env, ast);
        },
    }
}

pub fn formatResult(writer: anytype, results: *const solver.Result, env: *const named.Env, ast: *const Ast.AST) !void {
    _ = try writer.write("errors:\n");
    for (results.errors.items) |err| {
        try formatError(writer, err, env, ast);
        _ = try writer.write("\n");
    }

    try formatInferences(writer, &results.inferences, env, ast);
}
