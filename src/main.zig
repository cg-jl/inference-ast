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

    var ty_builder = lower.TypeBuilder.init(arena.allocator());
    defer ty_builder.deinit();

    // ScopeEnv creates its own arena allocator so I'll just give it GPA.
    var scope_env = scope.Env.init(gpa.allocator());
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
    try lower.walk_decl(unify_2_index, &ast, &scope_env, &ty_builder, &env, &constraints);

    stdout.print("ast: ", .{}) catch {};
    Ast.format_ast_node(stdout, unify_1_index, &ast) catch {};
    stdout.print("\n", .{}) catch {};
    try bw.flush();

    var result = try solver.solve(constraints, &env.core_env);

    try drop_temps(&result.inferences, &env);
    defer result.deinit();

    try format.result(stdout, &result, &env, &ast);
    try stdout.print("\n", .{});

    try bw.flush(); // don't forget to flush!
}

test "some test" {
    try main();
}
