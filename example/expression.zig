const std = @import("std");
const parcom = @import("parcom");

fn evaluate(expression: []const u8) u32 {
    _ = expression;
    return 0;
}

test {
    try std.testing.expectEqual(42, evaluate("11 + (24 - 5) + 6 * 2"));
}
