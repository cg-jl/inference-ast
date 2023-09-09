const std = @import("std");

const core = @import("core.zig");
const solver = @import("solver.zig");
const named = @import("named.zig");
const Ast = @import("ast.zig");
const format = @import("format.zig");
const scope = @import("scope.zig");
const lower = @import("lower.zig");

const log = std.log.scoped(.main);

const Ty = core.Ty;

fn dropTemps(inferences: *solver.Map, env: *const named.Env) !void {
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

fn buildUnify2(builder: *Ast.Builder) !u16 {
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
    const arg0 = Ast.Node.apply(inference_lookup.lookup_node, a.lookup_node);
    const arg1 = Ast.Node.lookup(k.name_index);

    return try builder.ast.decl(unify.name_index, &.{ arg0, arg1 }, res, &.{});
}

fn buildUnify1(builder: *Ast.Builder) !u16 {

    // unify (Inference a) (Inference b) =
    //  if a == b then Right Empty else Right (Infer a (Inference b))

    const right = try builder.cachedName("Right");
    const infer = try builder.cachedName("Infer");
    const inference = try builder.cachedName("Inference");
    const a = try builder.cachedName("a");
    const b = try builder.cachedName("b");
    const eq = try builder.cachedName("(==)");
    const unify = try builder.cachedName("unify");
    const empty = try builder.cachedName("Empty");

    // Right Empty
    const then_part = try builder.ast.apply(right.lookup_node, empty.lookup_node);

    // (Inference b)
    const inference_b = try builder.ast.apply(inference.lookup_node, b.lookup_node);

    // Right (Infer a (Inference b))
    const else_part = try builder.ast.apply(right.lookup_node, try builder.ast.apply(
        try builder.ast.apply(infer.lookup_node, a.lookup_node),
        inference_b,
    ));

    // ((==) a) b
    const condition = try builder.ast.apply(
        try builder.ast.apply(eq.lookup_node, a.lookup_node),
        b.lookup_node,
    );

    // if a == b then Right Empty else Right (Infer a (Inference b))
    const unify_res = try builder.ast.pushIf(condition, then_part, else_part);

    return try builder.ast.decl(
        unify.name_index,
        &.{
            Ast.Node.apply(inference.lookup_node, a.lookup_node),
            Ast.Node.apply(inference.lookup_node, b.lookup_node),
        },
        unify_res,
        &.{},
    );
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

    var ty_builder = lower.TypeBuilder.init(arena.allocator());
    defer ty_builder.deinit();

    // ScopeEnv creates its own arena allocator so I'll just give it GPA.
    var scope_env = scope.Env.init(gpa.allocator());
    defer scope_env.deinit();

    // root
    _ = try scope_env.createScope(null);

    const stdout_file = std.io.getStdOut().writer();
    var bw = std.io.bufferedWriter(stdout_file);
    const stdout = bw.writer();

    {
        const a_typevar = Ty{ .inference = try env.variable(.typevar, "a") };
        const e_typevar = Ty{ .inference = try env.variable(.typevar, "e") };
        const bool_ty = Ty{ .bound = .{ .id = try ty_builder.boundId("Bool", &env), .range = core.Range.empty() } };
        const func_bound_id = try ty_builder.boundId("(->)", &env);

        const unify_event_a = buildUnifyEv: {
            const start = try env.core_env.insertTy(env.alloc, a_typevar);
            break :buildUnifyEv Ty{ .bound = .{
                .id = try ty_builder.boundId("UnifyEvent", &env),
                .range = .{ .start = start, .end = start + 1 },
            } };
        };

        const unify_error_a = buildUnifyErr: {
            const start = try env.core_env.insertTy(env.alloc, a_typevar);
            break :buildUnifyErr Ty{ .bound = .{ .id = try ty_builder.boundId("UnifyError", &env), .range = .{ .start = start, .end = start + 1 } } };
        };

        const either_e_a = buildEither: {
            const bound_id = try ty_builder.boundId("Either", &env);
            const start = try env.core_env.insertTy(env.alloc, e_typevar);
            _ = try env.core_env.insertTy(env.alloc, a_typevar);
            break :buildEither Ty{ .bound = .{
                .id = bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        };

        try scope_env.addHint("Right", mkRight: {
            const start = try env.core_env.insertTy(env.alloc, a_typevar);
            _ = try env.core_env.insertTy(env.alloc, either_e_a);
            break :mkRight .{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        });

        try scope_env.addHint("Left", mkLeft: {
            const start = try env.core_env.insertTy(env.alloc, e_typevar);
            _ = try env.core_env.insertTy(env.alloc, either_e_a);
            break :mkLeft .{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        });

        {
            const a2bool = a2bool: {
                const start = try env.core_env.insertTy(env.alloc, a_typevar);
                _ = try env.core_env.insertTy(env.alloc, bool_ty);
                break :a2bool Ty{ .bound = .{ .id = func_bound_id, .range = .{ .start = start, .end = start + 2 } } };
            };

            const eq = eq: {
                const start = try env.core_env.insertTy(env.alloc, a_typevar);
                _ = try env.core_env.insertTy(env.alloc, a2bool);
                break :eq Ty{ .bound = .{ .id = func_bound_id, .range = .{ .start = start, .end = start + 2 } } };
            };

            try scope_env.addHint("(==)", eq);
        }

        const inference_ty_id = try ty_builder.boundId("InferenceTy", &env);

        const inference_ty_a = inferenceTy: {
            const start = try env.core_env.insertTy(env.alloc, a_typevar);
            break :inferenceTy Ty{ .bound = .{
                .id = inference_ty_id,
                .range = .{ .start = start, .end = start + 1 },
            } };
        };
        try scope_env.addHint("CyclicType", mkCT: {
            const start = try env.core_env.insertTy(env.alloc, inference_ty_a);
            _ = try env.core_env.insertTy(env.alloc, unify_error_a);
            break :mkCT .{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        });

        try scope_env.addHint("Infer", buildInfer: {
            // InferenceTy a -> UnifyEvent a
            const middle_param = try env.core_env.insertTy(env.alloc, inference_ty_a);
            _ = try env.core_env.insertTy(env.alloc, unify_event_a);

            // a -> (InferenceTy a -> UnifyEvent a)
            const start = try env.core_env.insertTy(env.alloc, a_typevar);
            _ = try env.core_env.insertTy(env.alloc, .{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = middle_param, .end = middle_param + 2 },
            } });
            break :buildInfer Ty{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        });

        try scope_env.addHint("Inference", inference: {
            const start = try env.core_env.insertTy(env.alloc, a_typevar);
            _ = try env.core_env.insertTy(env.alloc, inference_ty_a);
            break :inference .{ .bound = .{
                .id = func_bound_id,
                .range = .{ .start = start, .end = start + 2 },
            } };
        });
    }

    try scope_env.formatHintmap(stdout, &ast, &env);

    // constraints also go into GPA since its allocations are sporadic.
    var constraints = std.ArrayList(solver.Equation).init(gpa.allocator());

    var ast_arena = std.heap.ArenaAllocator.init(gpa.allocator());
    var ast_builder = Ast.Builder.init(ast_arena.allocator(), &ast);

    const unify_1_index = try buildUnify1(&ast_builder);

    stdout.print("unify: {}\n", .{ast.formatNode(unify_1_index)}) catch {};
    try bw.flush();

    const unify_2_index = try buildUnify2(&ast_builder);
    ast_builder.deinit();
    ast_arena.deinit();

    stdout.print("unify2: {}\n", .{ast.formatNode(unify_2_index)}) catch {};
    try bw.flush();

    try lower.walkDecl(unify_2_index, &ast, &scope_env, &ty_builder, &env, &constraints);

    var result = try solver.solve(constraints, &env.core_env);

    try dropTemps(&result.inferences, &env);
    defer result.deinit();

    try format.formatResult(stdout, &result, &env, &ast);
    try stdout.print("\n", .{});

    try bw.flush(); // don't forget to flush!
}

test "some test" {
    try main();
}
