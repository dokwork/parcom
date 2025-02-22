const std = @import("std");
const parcom = @import("parcom");
const P = parcom.Parsers;

test {
    std.testing.refAllDecls(@This());
}

test "parse a long sequence to slice" {
    // given:
    var sequence: [1024]u8 = undefined;
    for (0..sequence.len) |i| {
        sequence[i] = 'a';
    }
    const p = P.char('a').repeat(std.testing.allocator);
    // when:
    const result = (try p.parseString(std.testing.allocator, &sequence)).?;
    defer std.testing.allocator.free(result);
    // then:
    try std.testing.expectEqualSlices(u8, &sequence, result);
}
