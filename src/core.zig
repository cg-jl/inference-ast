const std = @import("std");
pub const Range = struct {
    start: u16,
    end: u16,

    pub fn is_empty(self: Range) bool {
        return self.start >= self.end;
    }

    pub fn len(self: Range) u16 {
        return self.end - self.start;
    }

    pub fn empty() Range {
        return .{ .start = 0, .end = 0 };
    }
};

pub const Ty = union(enum(u1)) {
    inference: u16,
    bound: struct { id: u16, range: Range },

    pub fn has_bound_args(self: Ty) bool {
        return switch (self) {
            .bound => |bound| !bound.range.is_empty(),
            else => false,
        };
    }
};

pub const Env = struct {
    // only soe types require to be stored, in order to reference them
    // when looping through a bound type.
    // This environment only does growing allocations, and only frees everything
    // when finished.
    tys: std.ArrayListUnmanaged(Ty) = .{},

    pub fn deinit(self: *Env, alloc: std.mem.Allocator) void {
        self.tys.deinit(alloc);
    }

    pub fn insert_ty(self: *Env, alloc: std.mem.Allocator, ty: Ty) !u16 {
        const id = self.tys.items.len;
        try self.tys.append(alloc, ty);
        return @truncate(u16, id);
    }

    pub fn view(self: *const Env, range: Range) []const Ty {
        return if (range.is_empty()) &[_]Ty{} else self.tys.items[range.start..range.end];
    }
};

pub fn format_ty(writer: anytype, ty: Ty, env: *const Env) !void {
    switch (ty) {
        .inference => |id| {
            try std.fmt.format(writer, "'{}", .{id});
        },

        .bound => |bound| {
            try std.fmt.format(writer, "#{}", .{bound.id});
            if (!bound.range.is_empty()) {
                _ = try writer.write("<");
                try format_ty(writer, env.tys.items[bound.range.start], env);
                for (env.tys.items[bound.range.start + 1 .. bound.range.end]) |child| {
                    _ = try writer.write(", ");
                    try format_ty(writer, child, env);
                }
                _ = try writer.write(">");
            }
        },
    }
}

pub fn substitute(inference: u16, target: Ty, env: *Env) void {
    for (env.tys.items) |*ty| {
        switch (ty.*) {
            .inference => |r| if (r == inference) {
                ty.* = target;
            },
            else => {},
        }
    }
}

pub fn occurs(inference: u16, ty: Ty, env: *const Env) bool {
    return switch (ty) {
        .inference => |id| id == inference,
        .bound => |bound| for (env.view(bound.range)) |tyi| {
            if (occurs(inference, tyi, env)) break true;
        } else false,
    };
}
