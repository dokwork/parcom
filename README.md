# parcom

[![parcom ci](https://github.com/dokwork/parcom/actions/workflows/ci.yml/badge.svg)](https://github.com/dokwork/parcom/actions/workflows/ci.yml)
[![codecov](https://codecov.io/gh/dokwork/parcom/branch/main/graph/badge.svg?token=OP8OVU42LV)](https://codecov.io/gh/dokwork/parcom)
![zig version](https://img.shields.io/badge/zig%20version-0.14.0-fcca77)

_Consume input, not memory._

This library provides an implementation of the parser combinators.

`Parcom` offers two options for consuming data:
 - parse the entire input string at once,
 - or consume and parse byte by byte from `AnyReader`.

When the input is a reader, `Parcom` works as a buffered reader. It reads few
bytes to the buffer and then parse them.

## Installation

Fetch `Parcom` from github:
```sh
zig fetch --save git+https://github.com/dokwork/parcom
```
Check that it was added to the list of dependencies in your `build.zig.zon` file:
```zig
...
    .dependencies = .{
        .parcom = .{
            .url = "git+https://github.com/dokwork/parcom#b93b8fb14f489007f27d42f8254f12b7d57d07da",
            .hash = "parcom-0.3.0-Hs8wfHFUAQBhhH-swYl1wrMLSh76uApvVzYBl56t90Ua",
        },
    },
```
Add `Parcom` module to your `build.zig`:
```zig
    const parcom = b.dependency("parcom", .{
        .target = target,
        .optimize = optimize,
    });
    ...
    exe.root_module.addImport("parcom", parcom.module("parcom"));
```

## Documentation
[https://dokwork.github.io/parcom/index.html](https://dokwork.github.io/parcom/index.html)

## Examples

 - [The parser of a math expression](examples/expression.zig)
 - [The json parser](examples/json.zig)

## Quick start

Let's create a parser, which will parse and execute a simple math expression with follow
grammar:
```
# The `number` is a sequence of unsigned integer numbers
Number := [0-9]+
# The `value` is a `number` or an `expression` in brackets
Value  := Number / '(' Expr ')'
# The `sum` is an operation of adding or substraction of two or more values
Sum    := Value (('+' / '-') Value)*
# The `expression` is result of evaluation the combination of values and operations
Expr   := evaluate(Sum)
```
Our parser will be capable of parsing and evaluating mathematical expressions
that include addition and subtraction operations, unsigned integers, and nested
expressions within brackets.

### A short API overview

Three different types of parser implementations exist:

 - The base parser implementations contain the logic for parsing input and serve
   as the fundamental building blocks;
 - The `ParserCombinator`provides methods to combine parsers and create new ones;
 - The `TaggedParser` erases the type of the underlying parser and simplifies
   the parser's type declaration.

Every parser provides the type of the parsing result as a constant `ResultType:
type`.

The result of parsing by any parser can be a value of type `ResultType` in successful
case, or `null` if parsing was failed. In successful case not whole input can be
consumed. If you have to be sure, that every byte was consumed and parsed, use the
[`end()`](https://dokwork.github.io/parcom/index.html#parcom.end) parser explicitly.

### Base parser

The `number` from the grammar above is a sequence of symbols from the range ['0', '9'].
Parcom has a constructor of the parser of bytes in a range, but we will create
our own parser starting from the base parser `AnyChar`. `AnyChar` is a simplest
parser consumed the input. It returns the next byte from the input, or
`null` if the input is empty.

To parse only numeric symbols we should provide a classifier - function that
receives the result of a parser and returns true only if it is an expected value:
```zig
const parcom = @import("parcom");

// ResultType: u8
const num_char = parcom.anyChar().suchThat({}, struct {
    fn condition(_: void, ch: u8) bool {
        return switch (ch) {
            '0' ... '9' => true,
            else => false,
        };
    }
}.condition);
```
Every function required i combinators in `Parcom` library has a `context` parameter.
That gives more flexibility for possible implementations of that functions.

### Repeat parsers

Next, we should continue applying our parser until we encounter the first
non-numeric symbol or reach the end of the input. To achieve this, we need to
store the parsed results. The simplest solution is to use a sentinel array:
```zig
// ResultType: [10:0]u8
const number = num_char.repeatToSentinelArray(.{ .max_count = 10 });
```
But that option is available only for parsers with scalar result types. For more
general cases a regular array can be used. If you know exact count of elements
in the parsed sequence, you can specified it to have an array with exact length
as result:
```zig
// ResultType: [3]u8
const number = num_char.repeatToArray(3);
```
However, this is a rare case. More often, the exact number of elements is
unknown, but the maximum number can be estimated: 
```zig
// ResultType: struct { [10]u8, usize }
const number = num_char.repeatToArray(.{ .max_count = 10 });
```
In such cases, the result is a tuple consisting of the array and a count of the
parsed items within it.

For cases, when impossible to predict the maximum count we can allocate a slice
to store the parsed results:
```zig
// ResultType: []u8
const number = num_char.repeat(allocator, .{});

// Don't forget to free the memory, allocated for the slice!
```
or use an arbitrary storage and a function to add an item to it:
```zig
var list = std.ArrayList(u8).init(allocator);
defer list.deinit();
// ResultType: *std.ArrayList(u8)
const p = anyChar().repeatTo(&list, .{}, std.ArrayList(u8).append);
```

Notice, that no matter which combinator you use to collected repeated numbers,
you have to set the `.min_count` to 1, because of empty collection of chars is
not a number!
```zig
// ResultType: []u8
const number = num_char.repeat(allocator, .{ .min_count = 1 });
```

**RepeatOptions**

All repeated combinators except the `repeatToArray(usize)` receive the `RepeatOptions`,
a structure with minimum and maximum counts of the elements in the sequence. All
parsers stop when reach the maximum count and fail if don't reach the minimum.

### Try one or try another

We'll postpone the `value` parser for now, and instead of that will focus on
creating a parsers for the '+' and '-' symbols.
```zig
// ResultType: i32
const value: ParserCombinator(???) = ???; 
```

First of all, we should be able to parse every symbol separately. The `char`
parser is the best candidate for it:
```zig
const plus = parcom.char('+');
const minus = parcom.char('-');
```
Next, we have to choose one of them. To accomplish this, let's combine parsers
to a new one, that first attempt one, and if it fails, it will try the other:
```zig
// ResultType: parcom.Either(u8, u8)
const plus_or_minus = plus.orElse(minus);
```
The result type of the new parser is `parcom.Either(L, R)`, an alias for
`union(enum) { left: L, right: R }` type.

### Combine results

We have a parser for operations and we assume that we have a parser for
values as well. This is sufficient to build the `Sum` parser, which, as you
may recall, follows this structure:
```
Sum := Value (('+' / '-') Value)*
```
Let's start from the part in brackets. We have to combine the `plus_or_minus` parser
with `value` parser and repeat result:
```zig
// ResultType: []struct{ parcom.Either(u8, u8), i32 }
plus_or_minus.andThen(value).repeat(allocator, .{});
```
The `andThen` combinator runs the left parser and then the right. If both
parsers were successful, it returns a tuple of results. Finally, we can combine
the value with the new parser to have the version of the `expression`
parser that follows the grammar:
```zig
// ResultType: struct{ i32, []struct{ parcom.Either(u8, u8), i32 } }
const sum = value.andThen(plus_or_minus.andThen(value).repeat(allocator, .{}));
```

### Transform the result

So far so good. We are ready to create a parser that will not only parse the input, but
also sum of parsed values:
```zig
const expr = sum.transform(i32, {}, struct {
    fn evaluate(_: void, value: struct{ i32, []struct{ Either(u8, u8), i32 } }) !i32 {
        var result: i32 = value[0];
        for (value[1]) |op_and_arg| {
            switch(op_and_arg[0]) {
                .left => result += op_and_arg[1],
                .right => result -= op_and_arg[1],
            )
        }
        return result;
    }
}.evaluate);
```
The combinator `transform` requires a context and a function for transformation. It
runs the left parser and applies the function to the parsed result.

### Tagged parser

Now the time to build the `value` parser:
```
Value  := Number / '(' Expr ')'
```
This is a recursive parser that not only forms part of the `expression` parser but
also depends on it. How we can implement this? First of all, let's wrap the
`expression` parser to the function:
```zig
const std = @import("std");
const parcom = @import("parcom");

fn expression(allocator: std.mem.Allocator) ??? {

    // ResultType: u8
    const num_char = parcom.anyChar().suchThat({}, struct {
        fn condition(_: void, ch: u8) bool {
            return switch (ch) {
                '0' ... '9' => true,
                else => false,
            };
        }
    }.condition);

    // ResultType: i32
    const number = num_char.repeat(allocator, .{ .min_count = 1 }).transform(i32, {}, struct {
        fn parseInt(_: void, value: []u8) !i32 {
            return try std.fmt.parseInt(i32, value, 10);
        }
    }.parseInt);

    // ResultType: i32
    const value = ???;

    // ResultType: parcom.Either(u8, u8)
    const plus_or_minus = parcom.char('+').orElse(parcom.char('-'));

    // ResultType: struct{ i32, []struct{ parcom.Either(u8, u8), i32 } }
    const sum = value.andThen(plus_or_minus.andThen(value).repeat(allocator, .{}));

    const expr = sum.transform(i32, {}, struct {
        fn evaluate(_: void, v: struct{ i32, []struct{ parcom.Either(u8, u8), i32 } }) !i32 {
            var result: i32 = v[0];
            for (v[1]) |op_and_arg| {
                switch(op_and_arg[0]) {
                    .left => result += op_and_arg[1],
                    .right => result -= op_and_arg[1],
                }
            }
            return result;
        }
    }.evaluate);

    return expr;
}
```
The type of `ParserCombinator` in `Parcom` can be very cumbersome, and it is
often impractical to manually declare it as a function's type. However, Zig
requires this type to allocate enough memory for the parser instance.
While most parsers in `Parcom` are simply namespaces, this is not true for all
of them. What can we do is moving our parser to heap and replace particular type
by the pointer to it. This is exactly how the `TaggedParser` works. It has a
pointer to the original parser, and a pointer to a function responsible for
parsing the input. More over, the `TaggedParser` has explicit `ResultType`:
```zig
const std = @import("std");
const parcom = @import("parcom");

fn expression(allocator: std.mem.Allocator) parcom.TaggedParser(i32) {
    ...
    return expr.taggedAllocated(allocator);
}
```

### Deferred parser

Let's go ahead and finally build the `value` parser:
```zig
const value = number.orElse(
    parcom.char('(').rightThen(expression(allocator)).leftThen(parcom.char(')')
);
```
Pay attention on `rightThen` and `leftThen` combinators. Unlike the `andThen`
combinator, these two do not produce a tuple. Instead, they ignore one value and
return another. The `rightThen` uses only result of the right parser, and
`leftThen` of the left parser respectively. It means, that both brackets will be
parsed, but ignored in the example above.

But this is not all. Unfortunately, such implementation of the `value`
parser will lead to infinite loop of invocations the `expression` function. We
can solve this by invoking the function only when we need to parse an expression
within brackets. The `Parcom` has the `deferred` parser for such purposes.
It receives the `ResultType` of `TaggedParser` which should be returned by the function,
a context that should be passed to the function and pointer to the function:

```zig
const value = number.orElse(
    parcom.char('(').rightThen(parcom.deferred(i32, allocator, expression)).leftThen(parcom.char(')'))
);
```
When the tagged parsed completes its deferred work, the `deinit` method will be
invoked, and memory will be freed. But, do not forget to invoke `deinit`
manually, when you create the `TaggedParser` outside the `deferred` parser!

<details>
  <summary>Complete solution</summary>
  
```zig
const std = @import("std");
const parcom = @import("parcom");

fn expression(allocator: std.mem.Allocator) !parcom.TaggedParser(i32) {

    // ResultType: u8
    const num_char = parcom.anyChar().suchThat({}, struct {
        fn condition(_: void, ch: u8) bool {
            return switch (ch) {
                '0' ... '9' => true,
                else => false,
            };
        }
    }.condition);

    // ResultType: i32
    const number = num_char.repeat(allocator, .{ .min_count = 1 }).transform(i32, {}, struct {
        fn parseInt(_: void, value: []u8) !i32 {
            return try std.fmt.parseInt(i32, value, 10);
        }
    }.parseInt);

    // ResultType: i32
    const value = number.orElse(
        parcom.char('(').rightThen(parcom.deferred(i32, allocator, expression)).leftThen(parcom.char(')'))
    )
    .transform(i32, {}, struct {
        fn getFromEither(_: void, v: parcom.Either(i32, i32)) !i32 {
            return switch (v) {
                .left => v.left,
                .right => v.right,
            };
        }
    }.getFromEither);

    // ResultType: parcom.Either(u8, u8)
    const plus_or_minus = parcom.char('+').orElse(parcom.char('-'));

    // ResultType: struct{ i32, []struct{ parcom.Either(u8, u8), i32 } }
    const sum = value.andThen(plus_or_minus.andThen(value).repeat(allocator, .{}));

    // ResultType: i32
    const expr = sum.transform(i32, {}, struct {
        fn evaluate(_: void, v: struct{ i32, []struct{ parcom.Either(u8, u8), i32 } }) !i32 {
            var result: i32 = v[0];
            for (v[1]) |op_and_arg| {
                switch(op_and_arg[0]) {
                    .left => result += op_and_arg[1],
                    .right => result -= op_and_arg[1],
                }
            }
            return result;
        }
    }.evaluate);

    return expr.taggedAllocated(allocator);
}

test "9-(5+2) == 2" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const parser = try expression(arena.allocator());
    try std.testing.expectEqual(2, try parser.parseString("9-(5+2)"));
}
```
  
</details>

### Cutting the input

In some cases it is reasonable not to consume the entire input to the string, and
instead parse it on-the-fly. For such cases, the `Parcom` library provides the
`parseFromReader` method, which takes a `std.io.AnyReader` as the input. During the
parsing, all consumed bytes are stored in an internal buffer to make it possible
to rollback the input and try another parser (such as with the `orElse` combinator).
While this approach may lead to the same result as reading the whole input to the string,
rollback may not make sense for some parsers. For example, when parsing JSON,
encountering the '{' symbol means the entire JObject must be parsed. If parsing
cannot proceed, it indicates that the input is malformed, and all parsers will
failed. It means, that the input can be cropped right before the '{' symbol.

In the example above can be reasonable to cut the input when the left brace is
parsed:
```zig
...
const value = number.orElse(
    parcom.char('(').cut().rightThen(parcom.deferred(i32, allocator, expression)).leftThen(parcom.char(')'))
//         added this ^
)
...
```

Cropping the input, when possible, can significantly reduce required memory and
may improve the speed of parsing. See [this example](examples/json.zig) for more details.

### Debug

When something is going wrong during the parsing, and a correct at first glance
parser returns null, it can be difficult to understand the root cause without
additional insights. In `Parcom` you can turn on logging for any particular
parser to see how it works during the parsing. For example, let's turn on
logging for the expression parser from the example above (with added `cut`
combinator)
```zig
...
    return expr.logged(.{ .label = "EXPR", .scope = .example }).taggedAllocated(allocator);
}
```
and run it on a string with unexpected symbol '!':
```zig
test "parse unexpected symbol" {
    // don't forget to turn on debug level for the test
    std.testing.log_level = .debug;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const parser = try expression(arena.allocator());
    try std.testing.expectEqual(2, try parser.parseString("9-(!5+2)"));
}
```
Now, we have enough insights to understand what happened and where it occurred:
```
error: 'expression.test.parse unexpected symbol' failed: [example] (debug):
The parsing by the <EXPR> has been started from position 0:
[9]-(!5+2)
[example] (debug):
The parsing by the <EXPR> has been started from position 3:
…[!]5+2)
[example] (debug): The parsing is failed at position 3:
…[!]5+2)
[example] (debug): End parsing by the <EXPR>. Cut 3 items during the parsing process.
[parcom] (warn): Imposible to reset the input from 3 to 2 at position 3:
…[!]5+2).
[example] (debug): An error error.ResetImposible occured on parsing by <EXPR> at position 3:
…[!]5+2)
[example] (debug): End parsing by the <EXPR>. Cut 3 items during the parsing process.
```
