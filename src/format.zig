const solver = @import("solver.zig");
const named = @import("named.zig");
const Ast = @import("ast.zig");

pub fn format_constraints(writer: anytype, constraints: []const solver.Equation, env: *const named.Env, ast: *const Ast.AST) !void {
    for (constraints) |c| {
        try Ast.format_ty(writer, c.lhs, env, ast);
        _ = try writer.write(" = ");
        try Ast.format_ty(writer, c.rhs, env, ast);
        _ = try writer.write("\n");
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

pub fn format_result(writer: anytype, results: *const solver.Result, env: *const named.Env, ast: *const Ast.AST) !void {
    _ = try writer.write("errors:\n");
    for (results.errors.items) |err| {
        try format_error(writer, err, env, ast);
        _ = try writer.write("\n");
    }

    try format_inferences(writer, &results.inferences, env, ast);
}
