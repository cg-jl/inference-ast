const std = @import("std");
pub const Range = struct {
    start: u16,
    end: u16,

    pub fn isEmpty(self: Range) bool {
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

    pub fn hasBoundArgs(self: Ty) bool {
        return switch (self) {
            .bound => |bound| !bound.range.isEmpty(),
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

    pub fn insertTy(self: *Env, alloc: std.mem.Allocator, ty: Ty) !u16 {
        const id = self.tys.items.len;
        try self.tys.append(alloc, ty);
        return @as(u16, @truncate(id));
    }

    pub fn view(self: *const Env, range: Range) []const Ty {
        return if (range.isEmpty()) &[_]Ty{} else self.tys.items[range.start..range.end];
    }
};

const FormatTy = struct {
    ty: Ty,
    env: *const Env,

    pub fn format(
        f: FormatTy,
        comptime _: []const u8,
        _: std.fmt.FormatOptions,
        w: anytype,
    ) @TypeOf(w).Error!void {
        switch (f.ty) {
            .inference => |id| return std.fmt.format(w, "'{}", .{id}),
            .bound => |bound| {
                try std.fmt.format(w, "#{}", .{bound.id});
                const children = f.env.view(bound.range);
                if (children.len != 0) {
                    try w.writeAll("<");
                    try std.fmt.format(w, "<{}", .{formatTy(children[0], f.env)});
                    for (children[1..]) |child| {
                        try std.fmt.format(w, ", {}", .{formatTy(child, f.env)});
                    }
                    return w.writeAll(">");
                }
            },
        }
    }
};

pub fn formatTy(ty: Ty, env: *const Env) FormatTy {
    return .{ .ty = ty, .env = env };
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
