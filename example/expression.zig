//! This is a small example of the mathematics expression parser,
//! which parse only unsigned integers, brackets, [+-*/] operations,
//! and no spaces.
//!
//! This example can be run with expression at first argument:
//! ```
//! zig build example -- "1+1"
//! ```
const std = @import("std");
const parcom = @import("parcom");

const P = parcom.Parsers;

const Value = i8;

const Operation = enum {
    plus,
    minus,
    multiply,
    divide,

    fn invoke(self: Operation, left: Value, right: Value) Value {
        const result = switch (self) {
            .plus => left + right,
            .minus => left - right,
            .multiply => left * right,
            .divide => @divTrunc(left, right),
        };
        return result;
    }

    fn parse(_: void, char: u8) anyerror!Operation {
        return switch (char) {
            '+' => .plus,
            '-' => .minus,
            '*' => .multiply,
            '/' => .divide,
            else => error.UnknownOperation,
        };
    }
};

/// This function builds a parser which follow the next grammar:
/// ```
/// Expr    ← Sum
/// Sum     ← Product (('+' / '-') Product)*
/// Product ← Value (('*' / '/') Value)*
/// Value   ← [0-9]+ / '(' Expr ')'
/// ```
fn expr(alloc: std.mem.Allocator) !parcom.TaggedParser(Value) {
    // functions to transform parsers results
    const fns = struct {
        fn parseInt(_: void, str: [10:0]u8) anyerror!Value {
            const len = std.mem.len(@as([*:0]const u8, &str));
            return try std.fmt.parseUnsigned(Value, str[0..len], 10);
        }
        fn valueFromParens(_: void, result: struct { u8, Value, u8 }) anyerror!Value {
            return result[1];
        }
        fn valueFromEither(_: void, result: parcom.Either(Value, Value)) anyerror!Value {
            return switch (result) {
                .left => result.left,
                .right => result.right,
            };
        }
        fn calculate(
            allocator: std.mem.Allocator,
            value: struct { Value, []struct { Operation, Value } },
        ) anyerror!Value {
            // we don't need the slice after calculating operations in it
            defer allocator.free(value[1]);

            var a: Value = value[0];
            for (value[1]) |tuple| {
                a = tuple[0].invoke(a, tuple[1]);
            }
            return a;
        }
    };

    // brackets: Int <- (<exp>)
    const brackets = P.tuple(.{ P.char('('), P.lazy(Value, alloc, expr), P.char(')') })
        .transform(Value, {}, fns.valueFromParens);

    // we can't use Parsers.int to parse numbers here to avoid consumption of the '-' and '+'
    // number: Int <- \d+
    const number = P.range('0', '9').repeatToSentinelArray(1, 10)
        .transform(Value, {}, fns.parseInt);

    // value: Int <- <number>|<brackets>
    const value = number.orElse(brackets)
        .transform(Value, {}, fns.valueFromEither);

    // product: Int <- <value>([*/]<value>)*
    const product = blk: {
        const operation = P.oneCharOf("*/").transform(Operation, {}, Operation.parse);
        break :blk value.andThen(operation.andThen(value).repeat(alloc))
            .transform(Value, alloc, fns.calculate);
    };

    // sum: Int <- <product>([+-]<product>)*
    const sum = blk: {
        const operation = P.oneCharOf("+-").transform(Operation, {}, Operation.parse);
        break :blk product.andThen(operation.andThen(product).repeat(alloc))
            .transform(Value, alloc, fns.calculate);
    };

    return try sum.tagged(alloc);
}

fn evaluate(alloc: std.mem.Allocator, expression: []const u8) !?Value {
    const p = try expr(alloc);
    defer p.deinit();
    return try p.parseString(alloc, expression);
}

test "1+1" {
    try std.testing.expectEqual(2, try evaluate(std.testing.allocator, "1+1"));
}

test "11+(24-5)+6*2" {
    try std.testing.expectEqual(42, try evaluate(std.testing.allocator, "11+(24-5)+6*2"));
}

test "3+6*9-(5+4)*2+(6/2)" {
    try std.testing.expectEqual(42, try evaluate(std.testing.allocator, "3+6*9-(5+4)*2+(6/2)"));
}

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer if (gpa.deinit() == .leak) @panic("MEMORY LEAK DETECTED!");
    const alloc = gpa.allocator();

    var args = std.process.args();
    // skip the path to the program
    _ = args.next();

    const explanation = "The expression should contain only unsigned integers and follow symbols: +-*/()";
    const stdout = std.io.getStdOut().writer();
    if (args.next()) |expression| {
        if (try evaluate(alloc, expression)) |result|
            try stdout.print("{s} == {d}", .{ expression, result })
        else
            std.debug.print("Expression \"{s}\" was not parsed.\n{s}", .{ expression, explanation });
    } else {
        std.debug.print("Please, pass an expression to evaluate.\n{s}", .{explanation});
    }
}
