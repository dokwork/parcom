const std = @import("std");
const parcom = @import("parcom");

const log = std.log.scoped(.expression);

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer if (gpa.deinit() == .leak) @panic("MEMORY LEAK DETECTED!");
    const alloc = gpa.allocator();

    var args = std.process.args();
    const stdout = std.io.getStdOut().writer();
    if (args.next()) |expression| {
        if (try evaluate(alloc, expression)) |result|
            try stdout.print("{s} == {d}", .{ expression, result });
    }
}

fn evaluate(alloc: std.mem.Allocator, expression: []const u8) !?Value {
    var list = std.ArrayList(struct { Operation, Value }).init(alloc);
    defer list.deinit();

    const p = try expr(&list);
    return try p.parseString(alloc, expression);
}

test {
    std.testing.log_level = .debug;

//[expression] (info): 24 minus 5 = 19
//[expression] (info): 11 minus 5 = 6
//[expression] (info): 6 plus 19 = 25
//[expression] (info): 25 plus 6 = 31
//[expression] (info): 31 multiply 2 = 62
    try std.testing.expectEqual(42, try evaluate(std.testing.allocator, "11+(24-5)+6*2"));
}

const P = parcom.Parsers;

const Value = i8;

const Operation = enum {
    plus,
    minus,
    multiply,
    divide,

    fn apply(self: Operation, left: Value, right: Value) Value {
        const result = switch (self) {
            .plus => left + right,
            .minus => left - right,
            .multiply => left * right,
            .divide => @divTrunc(left, right),
        };
        log.info("{d} {s} {d} = {d}", .{ left, @tagName(self), right, result });
        return result;
    }

    fn parse(char: u8) anyerror!Operation {
        return switch (char) {
            '+' => .plus,
            '-' => .minus,
            '*' => .multiply,
            '/' => .divide,
            else => error.UnknownOperation,
        };
    }
};

/// Expr    ← Sum
/// Sum     ← Product (('+' / '-') Product)*
/// Product ← Value (('*' / '/') Value)*
/// Value   ← [0-9]+ / '(' Expr ')'
fn expr(context: *anyopaque) !parcom.TaggedParser(Value) {
    const fns = struct {
        fn valueFromParens(result: struct { u8, Value, u8 }) anyerror!Value {
            return result[1];
        }
        fn valueFromEither(result: parcom.Either(Value, Value)) anyerror!Value {
            return switch (result) {
                .left => result.left,
                .right => result.right,
            };
        }
        fn calculate(value: struct { Value, []struct { Operation, Value } }) anyerror!Value {
            var a: Value = value[0];
            for (value[1]) |tuple| {
                a = tuple[0].apply(a, tuple[1]);
            }
            return a;
        }
    };
    const lb = P.char('(');
    const rb = P.char(')');
    const parens = P.tuple(.{ lb, P.lazy(Value, context, expr), rb }).transform(Value, fns.valueFromParens).debug(.parens);
    const operation = P.oneCharOf("+-*/").transform(Operation, Operation.parse);
    const value = P.int(Value).orElse(parens).transform(Value, fns.valueFromEither).debug(.value);
    const product = product_blk: {
        const tail = operation.andThen(value);
        const list: *std.ArrayList(@TypeOf(tail).ResultType) = @ptrCast(@alignCast(context));
        break :product_blk value.andThen(tail.repeatToList(list)).transform(Value, fns.calculate).debug(.product);
    };
    var sum = sum_blk: {
        const tail = operation.andThen(product);
        const list: *std.ArrayList(@TypeOf(tail).ResultType) = @ptrCast(@alignCast(context));
        break :sum_blk product.andThen(tail.repeatToList(list)).transform(Value, fns.calculate).debug(.sum);
    };

    return sum.tagged();
}
