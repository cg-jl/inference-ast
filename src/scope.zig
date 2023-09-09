const std = @import("std");
const core = @import("core.zig");
const Ast = @import("ast.zig");
const named = @import("named.zig");
const Ty = core.Ty;

pub const Env = struct {
    const Self = @This();

    const HintMap = std.StringHashMapUnmanaged(Ty);
    pub fn formatHintmap(self: *const Self, w: anytype, ast: *const Ast.AST, env: *const named.Env) void {
        std.fmt.format(w, "hints in current scope:\n", .{}) catch {};
        var iter = self.scopes.items[self.current_scope].hints.iterator();
        while (iter.next()) |i| {
            std.fmt.format(w, "{s} = ", .{i.key_ptr.*}) catch {};
            Ast.formatTy(w, i.value_ptr.*, env, ast) catch {};
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

        pub fn define(self: *Scope, name: []const u8, env: *named.Env, alloc: std.mem.Allocator) !u16 {
            const get_or_put = try self.variables.getOrPut(alloc, name);

            // if we had another definition, reuse that index instead of wasting space.
            // this way we can also point all definitions of the inference to the new set,
            // so that things declared initially as 'unknown' get redirected to the new sample.
            if (!get_or_put.found_existing) {
                const inf = try env.createVar(.variable, name);
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

    pub fn createScope(self: *Self, parent: ?ScopeIndex) !ScopeIndex {
        const len = @as(ScopeIndex, @truncate(self.scopes.items.len));
        try self.scopes.append(self.arena.allocator(), .{ .parent = parent, .variables = .{}, .hints = .{} });
        return len;
    }

    // NOTE: this is currently replacing stuff resulting from expressions
    pub fn unknown(self: *Self, env: *named.Env) !u16 {
        const inference_index = try env.unknown(self.unknown_count);
        self.unknown_count += 1;
        return inference_index;
    }

    pub fn switchToScope(self: *Self, scope: ScopeIndex) ScopeIndex {
        const old_scope = self.current_scope;
        self.current_scope = scope;
        return old_scope;
    }

    pub fn addHint(self: *Self, name: []const u8, ty: Ty) !void {
        try self.scopes.items[self.current_scope].hints.put(self.arena.allocator(), name, ty);
    }

    pub fn get(self: *Self, name: []const u8, env: *named.Env) !Ty {
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
                        break h;
                    if (self.scopes.items[current_scope].parent) |p| {
                        current_scope = p;
                    } else break null;
                };
            };

            break :instantiate_unknown if (found_hint) |hint| try env.instantiate(hint) else Ty{ .inference = try env.variable(.variable, name) };
        };

        return final_inference;
    }

    pub fn define(self: *Self, name: []const u8, env: *named.Env) !u16 {
        return try self.scopes.items[self.current_scope].define(name, env, self.arena.allocator());
    }
};
