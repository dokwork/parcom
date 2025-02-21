const std = @import("std");
const parcom = @import("parcom");

test {
    std.testing.refAllDecls(@This());
}
