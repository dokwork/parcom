// MIT License
//
// Copyright (c) 2025 Vladimir Popov <vladimir@dokwork.ru>
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

//! This library provides an implementation of the parser combinators.
//!
//! Three different types of parser implementations exist:
//! 1.  The inner parser implementations, which contain the logic for parsing the input.
//! 2.  The public wrapper `ParserCombinator`, which provides methods to combine parsers and create new ones.
//! 3.  The public wrapper `TaggedParser`, which erase the type of the underlying parser in `ParserCombinator`,
//!     allowing for explicit type declaration in the code.
//!
//! Github page: [https://github.com/dokwork/parcom](https://github.com/dokwork/parcom)
const std = @import("std");

const log = std.log.scoped(.parcom);

/// Creates a parser that doesn't read any bytes from the input,
/// and always returns passed value as the result.
pub fn successfull(result: anytype) ParserCombinator(Successfull(@TypeOf(result))) {
    return .{ .underlying = .{ .result = result } };
}

/// Creates a parser that fails if the input buffer contains not handled items, or otherwise
/// tries to consume one byte from the input, and completes successfully if `EndOfStream`
/// happened. It similar to '$' in regexp.
/// Example:
/// ```zig
/// test {
///     try std.testing.expectEqual({}, try end().parseString(""));
///     try std.testing.expectEqual(null, try end().parseString("anything"));
/// }
/// ```
pub fn end() ParserCombinator(End) {
    return .{ .implementation = .{} };
}

test end {
    try std.testing.expectEqual({}, try end().parseString(""));
    try std.testing.expectEqual(null, try end().parseString("anything"));
}

/// Creates a parser that reads one byte from the input, and returns it as the result.
/// Example:
/// ```zig
/// test {
///     try std.testing.expectEqual('a', try anyChar().parseString("a"));
///     try std.testing.expectEqual(null, try anyChar().parseString(""));
/// }
/// ```
pub inline fn anyChar() ParserCombinator(AnyChar) {
    return .{ .implementation = .{} };
}

test anyChar {
    try std.testing.expectEqual('a', try anyChar().parseString("a"));
    try std.testing.expectEqual(null, try anyChar().parseString(""));
}

/// Creates a parser that reads one byte from the input, and returns `C` as the
/// result if the same byte was read.
/// Example:
/// ```zig
/// test {
///     try std.testing.expectEqual('a', try anyChar().parseString("a"));
///     try std.testing.expectEqual(null, try anyChar().parseString(""));
/// }
/// ```
pub fn char(comptime C: u8) ParserCombinator(Const(AnyChar, C)) {
    return .{ .implementation = .{ .underlying = AnyChar{} } };
}

test char {
    const p = char('a');
    try std.testing.expectEqual('a', try p.parseString("a"));
    try std.testing.expectEqual(null, try p.parseString("b"));
    try std.testing.expectEqual(null, try p.parseString(""));
}

/// Creates a parser that reads one byte from the input and returns it as the result
/// if it is present in the chars set.
pub inline fn oneCharOf(comptime chars: []const u8) ParserCombinator(OneCharOf(chars)) {
    return .{ .implementation = .{} };
}

test oneCharOf {
    const p = oneCharOf("ab");

    try std.testing.expectEqual('a', try p.parseString("a"));
    try std.testing.expectEqual('b', try p.parseString("b"));
    try std.testing.expectEqual(null, try p.parseString("c"));
}

/// Creates a parser that reads bytes from the input into the buffer as long as they
/// are in the chars set "+-0123456789_boXABCDF". Then it attempts to parse
/// the buffer as an integer using `std.fmt.parseInt`.
/// Example:
/// ```zig
/// test {
///     const p = int(i8);
///     const alloc = std.testing.allocator;
///     try std.testing.expectEqual(2, try p.parseString(alloc, "2"));
///     try std.testing.expectEqual(2, try p.parseString(alloc, "+2"));
///     try std.testing.expectEqual(-2, try p.parseString(alloc, "-2"));
///     try std.testing.expectEqual(2, try p.parseString(alloc, "0b10"));
///     try std.testing.expectEqual(8, try p.parseString(alloc, "0o10"));
///     try std.testing.expectEqual(10, try p.parseString(alloc, "0XA"));
/// }
/// ```
pub inline fn int(comptime T: type) ParserCombinator(Int(T, 128)) {
    return .{ .implementation = .{} };
}

test int {
    const p = int(i8);
    try std.testing.expectEqual(2, try p.parseString("2"));
    try std.testing.expectEqual(2, try p.parseString("+2"));
    try std.testing.expectEqual(-2, try p.parseString("-2"));
    try std.testing.expectEqual(2, try p.parseString("0b10"));
    try std.testing.expectEqual(8, try p.parseString("0o10"));
    try std.testing.expectEqual(10, try p.parseString("0XA"));
}

/// Creates a parser that processes a char from the chars set ['a'..'z', 'A'..'Z', '0'..'9'].
/// Example:
/// ```zig
/// test {
///     const p = letterOrNumber();
///     try std.testing.expectEqual('b', try p.parseString("b"));
///     try std.testing.expectEqual('A', try p.parseString("A"));
///     try std.testing.expectEqual('1', try p.parseString("1"));
///     try std.testing.expectEqual(null, try p.parseString("-"));
/// }
/// ```
pub inline fn letterOrNumber() ParserCombinator(Conditional("Letter or number", AnyChar, void)) {
    return .{
        .implementation = .{ .underlying = AnyChar{}, .context = {}, .conditionFn = struct {
            fn isLetterOrNumber(_: void, value: u8) bool {
                return switch (value) {
                    'a'...'z' => true,
                    'A'...'Z' => true,
                    '0'...'9' => true,
                    else => false,
                };
            }
        }.isLetterOrNumber },
    };
}

test letterOrNumber {
    const p = letterOrNumber();
    try std.testing.expectEqual('b', try p.parseString("b"));
    try std.testing.expectEqual('A', try p.parseString("A"));
    try std.testing.expectEqual('1', try p.parseString("1"));
    try std.testing.expectEqual(null, try p.parseString("-"));
}

/// Creates a parser that processes only passed sequence of chars.
/// Example:
/// ```zig
/// test {
///     try std.testing.expectEqualStrings("foo", &((try word("foo").parseString("foo")).?));
/// }
/// ```
pub inline fn word(comptime W: []const u8) ParserCombinator(
    Conditional(WordLabel(W), ArrayExactly(AnyChar, W.len), []const u8),
) {
    return .{
        .implementation = .{
            .underlying = ArrayExactly(AnyChar, W.len){ .underlying = AnyChar{} },
            .context = W,
            .conditionFn = struct {
                fn compareWords(expected: []const u8, parsed: [W.len]u8) bool {
                    return std.mem.eql(u8, expected, &parsed);
                }
            }.compareWords,
        },
    };
}

test word {
    try std.testing.expectEqualStrings("foo", &((try word("foo").parseString("foo")).?));
}

/// Creates a parser that processes characters within the ASCII range, where From is the lowest
/// character in the ASCII table and To is the highest, inclusive.
/// Example:
/// ```zig
/// test {
///     const p = range('A', 'C');
///     try std.testing.expectEqual('A', try p.parseString("A"));
///     try std.testing.expectEqual('B', try p.parseString("B"));
///     try std.testing.expectEqual('C', try p.parseString("C"));
///     try std.testing.expectEqual(null, try p.parseString("a"));
///     try std.testing.expectEqual(null, try p.parseString("D"));
/// }
/// ```
pub inline fn range(comptime From: u8, To: u8) ParserCombinator(Conditional(RangeLabel(From, To), AnyChar, void)) {
    comptime {
        std.debug.assert(From < To);
    }
    return .{
        .implementation = .{
            .underlying = AnyChar{},
            .context = {},
            .conditionFn = struct {
                fn isInRange(_: void, value: u8) bool {
                    return From <= value and value <= To;
                }
            }.isInRange,
        },
    };
}

test range {
    const p = range('A', 'C');
    try std.testing.expectEqual(null, try p.parseString("a"));
    try std.testing.expectEqual(null, try p.parseString("b"));
    try std.testing.expectEqual(null, try p.parseString("c"));
    try std.testing.expectEqual(null, try p.parseString("D"));
    try std.testing.expectEqual('A', try p.parseString("A"));
    try std.testing.expectEqual('B', try p.parseString("B"));
    try std.testing.expectEqual('C', try p.parseString("C"));
}

/// Creates a parser that sequentially applies all passed parsers, and returns a tuple of
/// all results.
/// Example:
/// ```zig
/// test {
///     const p = tuple(.{ char('a'), char('b'), char('c') });
///     try std.testing.expectEqual(.{ 'a', 'b', 'c' }, (try p.parseString("abcdef")).?);
/// }
/// ```
pub inline fn tuple(parsers: anytype) ParserCombinator(Tuple(@TypeOf(parsers))) {
    return .{ .implementation = .{ .parsers = parsers } };
}

test tuple {
    const p = tuple(.{ char('a'), char('b'), char('c') });
    try std.testing.expectEqual(.{ 'a', 'b', 'c' }, (try p.parseString("abcdef")).?);
}

/// Creates a parser that invokes the function `f` to create a tagged parser, which will be used
/// to parse the input. That tagged parser will be deinited at the end of parsing if the destructor is provided
/// (parser was create by the `taggedAllocated` method.
/// ```zig
/// test {
///    var result = std.ArrayList(u8).init(std.testing.allocator);
///    defer result.deinit();
///    // Grammar:
///    // List <- Cons | Nil
///    // Cons <- '(' Int List ')'
///    // Nil <- "Nil"
///    const parser = try struct {
///        // this parser accumulates the numbers from an input to the list in reverse order
///        // for simplicity of the example
///        fn reversedList(accumulator: *std.ArrayList(u8)) !TaggedParser(void) {
///            const nil = word("Nil");
///            const cons = tuple(.{ char('('), int(u8), deferred(void, accumulator, reversedList), char(')') });
///            const list = cons.orElse(nil);
///            var parser = list.transform(void, accumulator, struct {
///                fn append(acc: *std.ArrayList(u8), value: @TypeOf(list).ResultType) !void {
///                    switch (value) {
///                        .right => {},
///                        .left => |cns| try acc.append(cns[1]),
///                    }
///                }
///            }.append);
///            return parser.taggedAllocated(accumulator.allocator);
///        }
///    }.reversedList(&result);
///    defer parser.deinit();
///    //
///    std.debug.assert(try parser.parseString("(1(2(3Nil))))") != null);
///    try std.testing.expectEqualSlices(u8, &.{ 3, 2, 1 }, result.items);
///}
/// ```
pub inline fn deferred(
    comptime ResultType: type,
    context: anytype,
    f: *const fn (context: @TypeOf(context)) anyerror!TaggedParser(ResultType),
) ParserCombinator(Deffered(@TypeOf(context), ResultType)) {
    return .{
        .implementation = Deffered(@TypeOf(context), ResultType){ .context = context, .buildParserFn = f },
    };
}

test deferred {
    var result = std.ArrayList(u8).init(std.testing.allocator);
    defer result.deinit();
    // Grammar:
    // List <- Cons | Nil
    // Cons <- '(' Int List ')'
    // Nil <- "Nil"
    const parser = try struct {
        // this parser accumulates the numbers from an input to the list in reverse order
        // for simplicity of the example
        fn reversedList(accumulator: *std.ArrayList(u8)) !TaggedParser(void) {
            const nil = word("Nil");
            const cons = tuple(.{ char('('), int(u8), deferred(void, accumulator, reversedList), char(')') });
            const list = cons.orElse(nil);
            var parser = list.transform(void, accumulator, struct {
                fn append(acc: *std.ArrayList(u8), value: @TypeOf(list).ResultType) !void {
                    switch (value) {
                        .right => {},
                        .left => |cns| try acc.append(cns[1]),
                    }
                }
            }.append);
            return parser.taggedAllocated(accumulator.allocator);
        }
    }.reversedList(&result);
    defer parser.deinit();

    std.debug.assert(try parser.parseString("(1(2(3Nil))))") != null);
    try std.testing.expectEqualSlices(u8, &.{ 3, 2, 1 }, result.items);
}

/// The final version of the parser with tagged result type.
/// This version of the parser can be useful when the type of the
/// parser should be provided manually, as example, in the function signature.
/// Example:
/// ```zig
/// test {
///     var p = char('a');
///     const tg: TaggedParser(u8) = p.tagged();
///     defer tg.deinit();
///     try std.testing.expectEqual('a', try tg.parseString("a"));
/// }
/// ```
pub fn TaggedParser(comptime TaggedType: type) type {
    return struct {
        pub const ResultType = TaggedType;

        const Self = @This();

        const Destructor = struct {
            alloc: std.mem.Allocator,
            deinitFn: *const fn (alloc: std.mem.Allocator, underlying: *const anyopaque) void,
        };

        underlying: *const anyopaque,
        parseFn: *const fn (parser: *const anyopaque, input: *Input) anyerror!?ResultType,
        destructor: ?Destructor = null,

        inline fn parse(self: Self, input: *Input) anyerror!?ResultType {
            return try self.parseFn(self.underlying, input);
        }

        /// Deallocates memory with underlying parser if it was allocated on heap.
        pub inline fn deinit(self: Self) void {
            if (self.destructor) |ds|
                ds.deinitFn(ds.alloc, self.underlying);
        }

        /// This method is similar to the same method in `ParserCombinator`.
        pub fn parseAnyReader(self: Self, alloc: std.mem.Allocator, reader: std.io.AnyReader) !?ResultType {
            var input = try Input.buffered(alloc, reader);
            defer input.impl.buffered.deinit();
            return try self.parse(&input);
        }

        /// This method is similar to the same method in `ParserCombinator`.
        pub inline fn parseReader(self: Self, alloc: std.mem.Allocator, reader: anytype) !?ResultType {
            return try self.parseAnyReader(alloc, reader.any());
        }

        /// This method is similar to the same method in `ParserCombinator`.
        pub fn parseString(self: Self, str: []const u8) !?ResultType {
            var input = Input.string(str);
            return self.parse(&input);
        }

        pub fn combinator(self: Self) ParserCombinator(Self) {
            return .{ .implementation = self };
        }
    };
}

test TaggedParser {
    var p = char('a');
    const tg: TaggedParser(u8) = p.tagged();
    defer tg.deinit();

    try std.testing.expectEqual('a', try tg.parseString("a"));
}

/// The wrapper around an implementation of a parser. It provides methods
/// to combine parsers to build a new one.
pub fn ParserCombinator(comptime Implementation: type) type {
    return struct {
        pub const ResultType = Implementation.ResultType;

        const Self = @This();

        /// The underlying implementation of the parser
        implementation: Implementation,

        fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("{any}", .{self.implementation});
        }

        inline fn parse(self: Self, input: *Input) anyerror!?ResultType {
            return try self.implementation.parse(input);
        }

        pub fn parseAnyReader(self: Self, alloc: std.mem.Allocator, reader: std.io.AnyReader) !?ResultType {
            var input = try Input.buffered(alloc, reader);
            defer input.impl.buffered.deinit();
            return try self.parse(&input);
        }

        pub fn parseString(self: Self, str: []const u8) !?ResultType {
            var input = Input.string(str);
            return self.parse(&input);
        }

        /// It runs this parser to parse an input from the `reader`. The whole input
        /// will be persisted in the inner buffer during the parsing. The allocator is
        /// used to allocate memory for the inner buffer.
        pub inline fn parseReader(self: Self, alloc: std.mem.Allocator, reader: anytype) !?ResultType {
            return try self.parseAnyReader(alloc, reader.any());
        }

        /// Wraps the self parser into a tagged version, allowing the type of the underlying parser
        /// to be erased. Be cautious with the lifetime of the self parser. In most cases, the
        /// `taggedAllocated` method is safer.
        pub fn tagged(self: *Self) TaggedParser(ResultType) {
            const fns = struct {
                fn parse(ptr: *const anyopaque, input: *Input) anyerror!?ResultType {
                    const s: *const Self = @ptrCast(@alignCast(ptr));
                    return try s.parse(input);
                }
            };
            return .{ .underlying = self, .parseFn = fns.parse };
        }

        /// Allocates memory for underlying implementation using `alloc`
        /// and copies underlying parser to that memory. It makes possible to erase the type of the
        /// underlying parser. The `deinit` method of the returned TaggedParser should be invoked
        /// to free allocated memory.
        /// Example:
        /// ```zig
        /// test {
        ///     const p = char('a');
        ///     const tg: TaggedParser(u8) = try p.taggedAllocated(std.testing.allocator);
        ///     defer tg.deinit();
        ///     try std.testing.expectEqual('a', try tg.parseString("a"));
        /// }
        /// ```
        pub fn taggedAllocated(self: Self, alloc: std.mem.Allocator) !TaggedParser(ResultType) {
            const fns = struct {
                fn parse(ptr: *const anyopaque, input: *Input) anyerror!?ResultType {
                    const implementation: *const Implementation = @ptrCast(@alignCast(ptr));
                    return try implementation.parse(input);
                }
                fn deinit(allocator: std.mem.Allocator, ptr: *const anyopaque) void {
                    const implementation: *const Implementation = @ptrCast(@alignCast(ptr));
                    allocator.destroy(implementation);
                }
            };
            const on_heap = try alloc.create(Implementation);
            on_heap.* = self.implementation;
            return .{
                .underlying = on_heap,
                .parseFn = fns.parse,
                .destructor = .{
                    .alloc = alloc,
                    .deinitFn = fns.deinit,
                },
            };
        }

        ///  Combines self parser with other to create a new parser that applies both underlying parsers
        ///  to the input, producing a tuple of results from each.
        /// Example:
        /// ```zig
        /// test {
        ///     const p = char('a').andThen(char('b'));
        ///     try std.testing.expectEqual(null, try p.parseString("aa"));
        ///     try std.testing.expectEqual(null, try p.parseString("bb"));
        ///     try std.testing.expectEqual(.{ 'a', 'b' }, try p.parseString("ab"));
        /// }
        /// ```
        pub inline fn andThen(
            self: Self,
            other: anytype,
        ) ParserCombinator(AndThen(Implementation, @TypeOf(other.implementation))) {
            return .{ .implementation = .{ .left = self.implementation, .right = other.implementation } };
        }

        test andThen {
            const p = char('a').andThen(char('b'));
            try std.testing.expectEqual(null, try p.parseString("aa"));
            try std.testing.expectEqual(null, try p.parseString("bb"));
            try std.testing.expectEqual(.{ 'a', 'b' }, try p.parseString("ab"));
        }

        ///  Combines self parser with other to create a new parser that
        ///  applies both underlying parsers to the input, producing a result from the self parser.
        /// Example:
        /// ```zig
        /// test {
        ///     const p = char('a').leftThen(char('b'));
        ///     try std.testing.expectEqual(null, try p.parseString("aa"));
        ///     try std.testing.expectEqual(null, try p.parseString("bb"));
        ///     try std.testing.expectEqual('a', try p.parseString("ab"));
        /// }
        /// ```
        pub inline fn leftThen(
            self: Self,
            other: anytype,
        ) ParserCombinator(LeftThen(Implementation, @TypeOf(other.implementation))) {
            return .{
                .implementation = LeftThen(Implementation, @TypeOf(other.implementation)){
                    .underlying = .{ .left = self.implementation, .right = other.implementation },
                },
            };
        }

        test leftThen {
            const p = char('a').leftThen(char('b'));
            try std.testing.expectEqual(null, try p.parseString("aa"));
            try std.testing.expectEqual(null, try p.parseString("bb"));
            try std.testing.expectEqual('a', try p.parseString("ab"));
        }

        ///  Combines self parser with other to create a new parser that
        ///  applies both underlying parsers to the input, producing a result from the other parser.
        /// Example:
        /// ```zig
        /// test {
        ///     const p = char('a').rightThen(char('b'));
        ///     try std.testing.expectEqual(null, try p.parseString("aa"));
        ///     try std.testing.expectEqual(null, try p.parseString("bb"));
        ///     try std.testing.expectEqual('b', try p.parseString("ab"));
        /// }
        /// ```
        pub inline fn rightThen(
            self: Self,
            other: anytype,
        ) ParserCombinator(RightThen(Implementation, @TypeOf(other.implementation))) {
            return .{
                .implementation = RightThen(Implementation, @TypeOf(other.implementation)){
                    .underlying = .{ .left = self.implementation, .right = other.implementation },
                },
            };
        }

        test rightThen {
            const p = char('a').rightThen(char('b'));
            try std.testing.expectEqual(null, try p.parseString("aa"));
            try std.testing.expectEqual(null, try p.parseString("bb"));
            try std.testing.expectEqual('b', try p.parseString("ab"));
        }

        ///  Combines self parser with other to create a new parser that applies at first the self
        ///  parser, and if it was unsuccessful, applies the other. It returns tagged union with
        ///  `.left` value for the result from the self parser, or the `.right` value for the result
        ///  from the other parser.
        /// Example:
        /// ```zig
        /// test {
        ///     const p = char('a').orElse(char('b'));
        ///     try std.testing.expectEqual(Either(u8, u8){ .left = 'a' }, try p.parseString("a"));
        ///     try std.testing.expectEqual(Either(u8, u8){ .right = 'b' }, try p.parseString("b"));
        ///     try std.testing.expectEqual(null, try p.parseString("c"));
        /// }
        /// ```
        pub inline fn orElse(
            self: Self,
            other: anytype,
        ) ParserCombinator(OrElse(Implementation, @TypeOf(other.implementation))) {
            return .{ .implementation = .{ .left = self.implementation, .right = other.implementation } };
        }

        test orElse {
            const p = char('a').orElse(char('b'));

            try std.testing.expectEqual(Either(u8, u8){ .left = 'a' }, try p.parseString("a"));
            try std.testing.expectEqual(Either(u8, u8){ .right = 'b' }, try p.parseString("b"));
            try std.testing.expectEqual(null, try p.parseString("c"));
        }

        /// Explicitly sets the expected result type for parser. It can help solve type inference
        /// in some cases. Example:
        /// ```zig
        ///    const T = struct { u8, u8 };
        ///    var p = char('a').andThen(char('b')).coerce(T);
        ///    const tp: TaggedParser(T) = p.tagged();
        /// ```
        pub fn coerce(
            self: Self,
            comptime ExpectedResultType: type,
        ) ParserCombinator(Coerce(Implementation, ExpectedResultType)) {
            return .{ .implementation = .{ .underlying = self.implementation } };
        }

        test coerce {
            // This can't be compiled:
            // ```
            // var p = char('a').andThen(char('b'));
            // const tp: TaggedParser(struct { u8, u8 }) = p.tagged();
            // ```
            // Compilation error (approximately):
            // > expected type 'parcom.TaggedParser(parcom.test.coerce__struct_6193)',
            // > found 'parcom.TaggedParser(parcom.AndThen(...,97),...,98)).ResultType)'
            //
            // But this is ok:
            const T = struct { u8, u8 };
            var p = char('a').andThen(char('b')).coerce(T);
            const tp: TaggedParser(T) = p.tagged();
            _ = tp;
        }

        /// Wraps the self parser in a new one that returns `Either{ .right: void }` when the underlying fails.
        /// Example:
        /// ```zig
        /// test {
        ///     const p = char('a').optional();
        ///     try std.testing.expectEqual(Either(u8, void){ .left = 'a' }, p.parseString("a"));
        ///     try std.testing.expectEqual(Either(u8, void){ .right = {} }, p.parseString("b"));
        /// }
        /// ```
        pub fn optional(self: Self) ParserCombinator(OrElse(Implementation, Successfull(void))) {
            return .{
                .implementation = OrElse(Implementation, Successfull(void)){
                    .left = self.implementation,
                    .right = Successfull(void){ .result = {} },
                },
            };
        }

        test optional {
            const p = char('a').optional();
            try std.testing.expectEqual(Either(u8, void){ .left = 'a' }, p.parseString("a"));
            try std.testing.expectEqual(Either(u8, void){ .right = {} }, p.parseString("b"));
        }

        /// Wraps the self parser in a new one that applies the `condition` function to the result of
        /// the underlying parser and fails if the function returns `false`.
        pub inline fn suchThat(
            self: Self,
            context: anytype,
            condition: *const fn (ctx: @TypeOf(context), value: @TypeOf(self).ResultType) bool,
        ) ParserCombinator(Conditional("Such that", @TypeOf(self), @TypeOf(context))) {
            return .{
                .implementation = .{
                    .underlying = self.implementation,
                    .context = context,
                    .conditionFn = condition,
                },
            };
        }

        /// Wraps the self parser in a new one that repeat it until the underlying parser fails.
        /// All parsed results are stored in a slice allocated by the provided allocator.
        /// The returned slice must be freed using `free` method of the same allocator.
        /// Example:
        /// ```zig
        /// test {
        ///     var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
        ///     defer arena.deinit();
        ///     const alloc = arena.allocator();
        ///     const p = char('a').repeat(alloc, .{});
        ///     try std.testing.expectEqualSlices(u8, &[_]u8{}, (try p.parseString(alloc, "")).?);
        ///     try std.testing.expectEqualSlices(u8, &[_]u8{'a'}, (try p.parseString(alloc, "a")).?);
        ///     try std.testing.expectEqualSlices(u8, &[_]u8{ 'a', 'a' }, (try p.parseString(alloc, "aa")).?);
        ///     try std.testing.expectEqualSlices(u8, &[_]u8{ 'a', 'a' }, (try p.parseString(alloc, "aab")).?);
        /// }
        /// ```
        /// See documentation for `RepeatOptions` for more details.
        pub inline fn repeat(
            self: Self,
            alloc: std.mem.Allocator,
            comptime options: RepeatOptions,
        ) ParserCombinator(Slice(Implementation, options)) {
            RepeatOptions.validate(options);
            return .{ .implementation = .{ .underlying = self.implementation, .alloc = alloc } };
        }

        test repeat {
            var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
            defer arena.deinit();

            const p = char('a').repeat(arena.allocator(), .{});

            try std.testing.expectEqualSlices(u8, &[_]u8{}, (try p.parseString("")).?);
            try std.testing.expectEqualSlices(u8, &[_]u8{'a'}, (try p.parseString("a")).?);
            try std.testing.expectEqualSlices(u8, &[_]u8{ 'a', 'a' }, (try p.parseString("aa")).?);
            try std.testing.expectEqualSlices(u8, &[_]u8{ 'a', 'a' }, (try p.parseString("aab")).?);
        }

        /// Wraps the self parser in a new one, depending on the provided `options`. Possible valid
        /// options are:
        /// 1. Unsigned integer - if the `options` is a number, the new parser will be
        /// repeated until the passed number of items will be parsed, or the underlying parser
        /// fails. If the underlying parser fails before parsing enough items, the new parser
        /// fails. Otherwise, an array containing the count items is returned.
        /// 2. `RepeatOptions` - the new parser will be repeated until the `max_count` items will be
        /// parsed, or the underlying parser fails. If the underlying parser fails before producing
        /// `min_count` results, the new parser fails. Otherwise, a tuple with an array with size
        /// `max_count` and the count of parsed items will be returned.
        /// Example:
        /// ```zig
        /// test {
        ///     const p1 = char('a').repeatToArray(2);
        ///     try std.testing.expectEqualSlices(
        ///         u8,
        ///         &[_]u8{ 'a', 'a' },
        ///         &((try p1.parseString("aa")).?),
        ///     );
        ///     try std.testing.expectEqualSlices(
        ///         u8,
        ///         &[_]u8{ 'a', 'a' },
        ///         &((try p1.parseString("aaa")).?),
        ///     );
        ///     //
        ///     const p2 = char('a').repeatToArray(.{ .min_count = 2, .max_count = 3 });
        ///     try std.testing.expectEqual(null, try p2.parseString("a"));
        ///     const result = (try p2.parseString("aa")).?;
        ///     try std.testing.expectEqual(2, result.count);
        ///     try std.testing.expectEqualSlices(u8, &[_]u8{ 'a', 'a' }, result.items[0..result.count]);
        /// }
        /// ```
        pub inline fn repeatToArray(
            self: Self,
            comptime options: anytype,
        ) ParserCombinator(Array(Implementation, options)) {
            return .{ .implementation = .{ .underlying = self.implementation } };
        }

        test repeatToArray {
            const p1 = char('a').repeatToArray(2);
            //
            try std.testing.expectEqual(null, try p1.parseString(""));
            try std.testing.expectEqual(null, try p1.parseString("ab"));
            try std.testing.expectEqualSlices(
                u8,
                &[_]u8{ 'a', 'a' },
                &((try p1.parseString("aa")).?),
            );
            try std.testing.expectEqualSlices(
                u8,
                &[_]u8{ 'a', 'a' },
                &((try p1.parseString("aaa")).?),
            );
            //
            const p2 = char('a').repeatToArray(.{ .min_count = 2, .max_count = 3 });
            try std.testing.expectEqual(null, try p2.parseString("a"));
            const result = (try p2.parseString("aa")).?;
            try std.testing.expectEqual(2, result.count);
            try std.testing.expectEqualSlices(u8, &[_]u8{ 'a', 'a' }, result.items[0..result.count]);
        }

        /// Wraps the self parser in a new one that repeat it until the `max_count` results will be parsed,
        /// or the underlying parser fails. The new parser doesn't fail when the underlying doesn't
        /// produce `max_count` results. Instead, it set the sentinel element after the last
        /// parsed result to the final array. If count of parsed results is less than `min_count`, the
        /// returned parser fails.
        /// Example:
        /// ```zig
        /// test {
        ///     const p0 = char('a').repeatToSentinelArray(.{ .max_count = 2 });
        ///     //
        ///     var result: [2:0]u8 = (try p0.parseString("")).?;
        ///     try std.testing.expectEqual(0, result[0]);
        ///     //
        ///     const p = char('a').repeatToSentinelArray(.{ .min_count = 1, .max_count = 2 });
        ///     try std.testing.expectEqual(null, try p.parseString(""));
        ///     //
        ///     result = (try p.parseString("ab")).?;
        ///     try std.testing.expectEqual('a', result[0]);
        ///     try std.testing.expectEqual(0, result[2]);
        ///     //
        ///     result = (try p.parseString("aa")).?;
        ///     try std.testing.expectEqual('a', result[0]);
        ///     try std.testing.expectEqual('a', result[1]);
        ///     try std.testing.expectEqual(0, result[2]);
        /// }
        /// ```
        pub inline fn repeatToSentinelArray(
            self: Self,
            comptime options: RepeatOptions,
        ) ParserCombinator(SentinelArray(Implementation, options)) {
            RepeatOptions.validate(options);
            return .{ .implementation = .{ .underlying = self.implementation } };
        }

        test repeatToSentinelArray {
            const p0 = char('a').repeatToSentinelArray(.{ .max_count = 2 });

            var result: [2:0]u8 = (try p0.parseString("")).?;
            try std.testing.expectEqual(0, result[0]);

            const p = char('a').repeatToSentinelArray(.{ .min_count = 1, .max_count = 2 });
            try std.testing.expectEqual(null, try p.parseString(""));

            result = (try p.parseString("ab")).?;
            try std.testing.expectEqual('a', result[0]);
            try std.testing.expectEqual(0, result[2]);

            result = (try p.parseString("aa")).?;
            try std.testing.expectEqual('a', result[0]);
            try std.testing.expectEqual('a', result[1]);
            try std.testing.expectEqual(0, result[2]);
        }

        /// Wraps the self parser in a new one that repeat the underlying parser until it fails,
        /// or consumed `max_count` items, if that limit is specified in the provided `RepeatOptions`.
        /// It applies the function `add_to_collection` to the every parsed item.
        /// Example:
        /// ```zig
        /// test {
        ///    var map = std.AutoHashMap(u8, u8).init(std.testing.allocator);
        ///    defer map.deinit();
        ///    //
        ///    const p = anyChar().andThen(anyChar()).repeatTo(&map, .{}, struct {
        ///        fn put(container: *std.AutoHashMap(u8, u8), values: struct { u8, u8 }) anyerror!void {
        ///            try container.put(values[0], values[1]);
        ///        }
        ///    }.put);
        ///    //
        ///    const result = (try p.parseString("1a2b")).?;
        ///    try std.testing.expectEqual('a', result.get('1'));
        ///    try std.testing.expectEqual('b', result.get('2'));
        /// }
        /// ```
        pub inline fn repeatTo(
            self: Self,
            collector: anytype,
            comptime options: RepeatOptions,
            add_to_collection: *const fn (ctx: @TypeOf(collector), ResultType) anyerror!void,
        ) ParserCombinator(RepeatTo(Implementation, @TypeOf(collector), options)) {
            RepeatOptions.validate(options);
            return .{
                .implementation = .{
                    .underlying = self.implementation,
                    .collector = collector,
                    .addFn = add_to_collection,
                },
            };
        }

        test repeatTo {
            var map = std.AutoHashMap(u8, u8).init(std.testing.allocator);
            defer map.deinit();
            //
            const p = anyChar().andThen(anyChar()).repeatTo(&map, .{}, struct {
                fn put(container: *std.AutoHashMap(u8, u8), values: struct { u8, u8 }) anyerror!void {
                    try container.put(values[0], values[1]);
                }
            }.put);
            //
            const result = (try p.parseString("1a2b")).?;
            try std.testing.expectEqual('a', result.get('1'));
            try std.testing.expectEqual('b', result.get('2'));
        }

        /// Wraps the self parser in a new one that applies the function `f` to the parsing result and
        /// returns the value produced by the function.
        /// Example:
        /// ```zig
        /// test {
        ///     const p = anyChar().repeatToArray(2).transform(u8, {}, struct {
        ///         fn parseInt(_: void, arr: [2]u8) anyerror!u8 {
        ///             return try std.fmt.parseInt(u8, &arr, 10);
        ///         }
        ///     }.parseInt);
        ///     //
        ///     try std.testing.expectEqual(42, try p.parseString("42"));
        /// }
        /// ```
        pub inline fn transform(
            self: Self,
            comptime Result: type,
            context: anytype,
            f: *const fn (ctx: @TypeOf(context), a: ResultType) anyerror!Result,
        ) ParserCombinator(Transform(Implementation, @TypeOf(context), Result)) {
            return .{ .implementation = .{ .underlying = self.implementation, .context = context, .transformFn = f } };
        }

        test transform {
            const p = anyChar().repeatToArray(2).transform(u8, {}, struct {
                fn parseInt(_: void, arr: [2]u8) anyerror!u8 {
                    return try std.fmt.parseInt(u8, &arr, 10);
                }
            }.parseInt);

            try std.testing.expectEqual(42, try p.parseString("42"));
        }

        /// Create a parser that writes the result of running the underlying
        /// parser to the log with passed scope and debug level.
        /// _Note: do not forget to add `std.testing.log_level = .debug;` to your test._
        pub fn debug(self: Self, comptime scope: @Type(.EnumLiteral)) ParserCombinator(Logged(Self, scope)) {
            return .{ .implementation = Logged(Self, scope){ .underlying = self } };
        }
    };
}

/// Alias for `union(enum) { left: A, right: B }`
pub fn Either(comptime A: type, B: type) type {
    return union(enum) { left: A, right: B };
}

/// Describes how the parser should be repeated.
/// By default, it may be repeated zero times or continue until a failure occurs.
/// If the `max_count` is provided, the parser will stop after parsing `max_count` items.
/// If the `min_count` is provided, and the count of parsing items less than `min_count`, the parser fails.
/// Note, the `min_count` must be less or equal to `max_count`.
pub const RepeatOptions = struct {
    /// The minimum count of items required for successful parsing (inclusive).
    min_count: usize = 0,
    /// The maximum count of items (inclusive).
    max_count: ?usize = null,

    pub fn validate(comptime self: RepeatOptions) void {
        if (self.max_count) |max_count| {
            if (self.min_count > max_count)
                @compileError(std.fmt.comptimePrint(
                    "The minimum count must be less or equal to the maximum count. {any}",
                    .{self},
                ));
            if (max_count == 0)
                @compileError(std.fmt.comptimePrint(
                    "The maximum count must be greater than zero. {any}",
                    .{self},
                ));
        }
    }

    /// Returns true if no more item should be parsed
    pub inline fn isEnough(self: RepeatOptions, count: usize) bool {
        if (self.max_count) |max_count| {
            return count >= max_count;
        }
        return false;
    }
};

/// An input for parsers. It can be tin wrapper around the whole input string,
/// or behave as a buffered reader.
const Input = struct {
    const Error = error{ResetImposible};

    const BufferedInput = struct {
        /// The reader of the original input
        /// It must be defined if the allocator is defined.
        reader: std.io.AnyReader,
        /// Inner buffer of the input
        buffer: std.ArrayList(u8),

        fn init(alloc: std.mem.Allocator, reader: std.io.AnyReader) !BufferedInput {
            return .{ .buffer = std.ArrayList(u8).init(alloc), .reader = reader };
        }

        /// Frees memory of the buffer
        fn deinit(self: BufferedInput) void {
            self.buffer.deinit();
        }
    };

    const Implementation = union(enum) {
        string_wrapper: struct {
            input_string: []const u8,
        },
        buffered: BufferedInput,
    };

    /// The initial size of the buffer.
    const init_size = 5;
    /// The count of bytes to read from the reader at once;
    const read_bytes_count = 128;

    /// An index of the element in the input that should be parsed next.
    /// This index includes the count of committed items.
    pos: usize = 0,
    /// An index of the element in the buffer from which the parsing has been started,
    /// and to which the parsing should rollback in case of fail.
    original_pos: usize = 0,
    /// A count of items from the beginning of the input that can't be parsed again.
    /// For the buffered input it equals to the total count of cropped items.
    committed_count: usize = 0,
    /// The current implementation of the input.
    impl: Implementation,

    /// Builds buffered input for parsers
    fn buffered(alloc: std.mem.Allocator, reader: std.io.AnyReader) !Input {
        return .{ .impl = .{ .buffered = try BufferedInput.init(alloc, reader) } };
    }

    /// Builds a wrapper around the string as the input for parsers
    fn string(str: []const u8) Input {
        return .{ .impl = .{ .string_wrapper = .{ .input_string = str } } };
    }

    /// Persists the current position to make it possible to reset back to it.
    /// This method must be invoked before parsing the input.
    fn startParsing(self: *Input) void {
        self.original_pos = self.pos;
    }

    /// Resets the current position back to the value persisted at
    /// `startParsing`.
    /// Returns `ResetImposible` error if the input was cut during the parsing
    /// and rolling back to the original position is impossible.
    fn reset(self: *Input) Error!void {
        if (self.original_pos == 0 or self.original_pos > self.committed_count) {
            self.pos = self.original_pos;
        } else {
            log.warn("The parser was failed after cut at {}", .{self.*});
            return Error.ResetImposible;
        }
    }

    /// For the buffered input this method drops all accumulated items till the current position;
    /// For the string input this method marks all items before the current position as unreachable.
    fn cut(self: *Input) void {
        self.committed_count = self.pos;
        if (self.impl == .buffered) {
            self.impl.buffered.buffer.shrinkRetainingCapacity(
                self.impl.buffered.buffer.items.len - self.committed_count,
            );
        }
    }

    /// Reads one byte from the input and increases the `idx` by one.
    ///
    /// If the underlying implementation is a buffered input, this method consume `read_bytes_count`
    /// from the original reader and caches it in the buffer. Then the item from the
    /// buffer on the `idx` position is returned.
    ///
    /// If the self is a string input, this method returns the item from the
    /// buffer on the `idx` position.
    ///
    /// If no items in both buffer and reader, then it means end of the input
    /// and null is returned.
    fn read(self: *Input) !?u8 {
        switch (self.impl) {
            .string_wrapper => |wrapper| {
                if (self.pos >= wrapper.input_string.len) {
                    return null;
                } else {
                    self.pos += 1;
                    return wrapper.input_string[self.pos - 1];
                }
            },
            .buffered => |*input| {
                var buf: [read_bytes_count]u8 = undefined;
                const len = try input.reader.read(&buf);
                if (len > 0) {
                    const idx = self.pos - self.committed_count;
                    try input.buffer.appendSlice(buf[0..len]);
                    std.debug.assert(idx < input.buffer.items.len - 1);
                    self.pos += 1;
                    return input.buffer.items[idx];
                } else {
                    return null;
                }
            },
        }
    }

    fn format(self: Input, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        const buffer: []const u8, const idx: usize = switch (self.impl) {
            .string_wrapper => |wrapper| .{ wrapper.input_string, self.pos },
            .buffered => |input| .{ input.buffer.items, self.pos - self.committed_count },
        };
        if (idx < buffer.len) {
            const left_bound = if (idx == 0) 0 else @min(idx - 1, buffer.len - 1);
            const right_bound = @min(idx + 1, buffer.len - 1);
            const symbol = switch (buffer[idx]) {
                '\n' => "\\n",
                '\r' => "\\r",
                '\t' => "\\t",
                else => &[_]u8{buffer[idx]},
            };
            try writer.print(
                "position {d}:\n{s}[{s}]{s}",
                .{ self.pos, buffer[0..left_bound], symbol, buffer[right_bound..] },
            );
        } else {
            try writer.print("position {d}:\n{s}[]", .{ self.pos, buffer });
        }
    }
};

fn WordLabel(comptime w: []const u8) *const [std.fmt.comptimePrint("Word {any}", .{w}).len:0]u8 {
    return std.fmt.comptimePrint("Word {any}", .{w});
}

fn RangeLabel(
    comptime From: u8,
    To: u8,
) *const [std.fmt.comptimePrint("Range of char from {c} to {c}", .{ From, To }).len:0]u8 {
    return std.fmt.comptimePrint("Range of char from {c} to {c}", .{ From, To });
}

fn Successfull(comptime T: type) type {
    return struct {
        pub const ResultType = T;
        result: ResultType,
        pub fn parse(self: @This(), _: *Input) anyerror!?ResultType {
            return self.result;
        }
    };
}

fn Failed(comptime T: type) type {
    return struct {
        pub const ResultType = T;
        pub fn parse(_: @This(), _: *Input) anyerror!?ResultType {
            return null;
        }
    };
}

const End = struct {
    pub const ResultType = void;

    pub fn parse(_: End, input: *Input) anyerror!?void {
        if (try input.read()) |_| {
            input.pos -= 1;
            return null;
        } else {
            return;
        }
    }

    fn format(_: AnyChar, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        try writer.writeAll("<End of input>");
    }
};

const AnyChar = struct {
    pub const ResultType = u8;

    pub fn parse(_: AnyChar, input: *Input) anyerror!?u8 {
        return try input.read();
    }

    fn format(_: AnyChar, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        try writer.writeAll("<any char>");
    }
};

fn Conditional(comptime Label: []const u8, Underlying: type, Context: type) type {
    return struct {
        const Self = @This();

        pub const ResultType = Underlying.ResultType;

        underlying: Underlying,
        context: Context,
        conditionFn: *const fn (ctx: Context, value: ResultType) bool,

        fn parse(self: Self, input: *Input) anyerror!?ResultType {
            input.startParsing();
            if (try self.underlying.parse(input)) |res| {
                if (self.conditionFn(self.context, res)) return res;
            }
            try input.reset();
            return null;
        }

        fn format(_: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.writeAll(std.fmt.comptimePrint("<{s}>", .{Label}));
        }
    };
}

fn Const(comptime Underlying: type, comptime template: Underlying.ResultType) type {
    return struct {
        const Self = @This();

        pub const ResultType = Underlying.ResultType;

        underlying: Underlying,

        fn parse(self: Self, input: *Input) anyerror!?ResultType {
            input.startParsing();
            if (try self.underlying.parse(input)) |res| {
                if (res == template) return res;
            }
            try input.reset();
            return null;
        }

        fn format(_: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.writeAll(std.fmt.comptimePrint("<Constant {any}>", .{template}));
        }
    };
}

fn Slice(comptime Underlying: type, options: RepeatOptions) type {
    return struct {
        const Self = @This();

        pub const ResultType = []Underlying.ResultType;

        const init_size = if (options.max_count) |value| value else 10;

        underlying: Underlying,
        alloc: std.mem.Allocator,

        fn parse(self: Self, input: *Input) anyerror!?ResultType {
            input.startParsing();
            var slice: ResultType = try self.alloc.alloc(Underlying.ResultType, init_size);
            errdefer self.alloc.free(slice);
            var count: usize = 0;
            while (!options.isEnough(count)) : (count += 1) {
                if (try self.underlying.parse(input)) |t| {
                    if (count == slice.len) {
                        slice = try self.alloc.realloc(slice, newSize(slice.len));
                    }
                    slice[count] = t;
                } else {
                    break;
                }
            }
            if (count < options.min_count) {
                self.alloc.free(slice);
                try input.reset();
                return null;
            }
            return try self.alloc.realloc(slice, count);
        }

        fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<Slice of {s}>", .{self.underlying});
        }

        inline fn newSize(current_len: usize) usize {
            return current_len * 17 / 10;
        }
    };
}

fn Array(comptime Underlying: type, options: anytype) type {
    const info = @typeInfo(@TypeOf(options));
    switch (info) {
        .Int, .ComptimeInt => return ArrayExactly(Underlying, options),
        .Struct => {
            RepeatOptions.validate(options);
            if (@as(RepeatOptions, options).max_count) |capacity| {
                return ArrayRange(Underlying, options.min_count, capacity);
            } else {
                @compileError("You have to provide or exact count or max count of expected items in array.");
            }
        },
        else => @compileError(
            std.fmt.comptimePrint(
                "Wrong options {any} for repeating parser. You should specify the exact number of expected items or provide the RepeatOptions structure.",
                .{info},
            ),
        ),
    }
}

fn ArrayExactly(comptime Underlying: type, count: u8) type {
    return struct {
        const Self = @This();

        pub const ResultType = [count]Underlying.ResultType;

        underlying: Underlying,

        fn parse(self: Self, input: *Input) anyerror!?ResultType {
            input.startParsing();
            var result: ResultType = undefined;
            for (0..count) |i| {
                if (try self.underlying.parse(input)) |t| {
                    result[i] = t;
                } else {
                    try input.reset();
                    return null;
                }
            }
            return result;
        }

        fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<Array of {s}>", .{self.underlying});
        }
    };
}

fn ArrayRange(comptime Underlying: type, min_count: usize, capacity: usize) type {
    return struct {
        const Self = @This();

        pub const ResultType = struct { items: [capacity]Underlying.ResultType, count: usize };

        underlying: Underlying,

        fn parse(self: Self, input: *Input) anyerror!?ResultType {
            input.startParsing();
            var count: usize = 0;
            var items: [capacity]Underlying.ResultType = undefined;
            while (count < capacity) {
                if (try self.underlying.parse(input)) |t| {
                    items[count] = t;
                    count += 1;
                } else {
                    break;
                }
            }
            if (count < min_count) {
                try input.reset();
                return null;
            } else {
                return .{ .items = items, .count = count };
            }
        }

        fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<Array of {s}>", .{self.underlying});
        }
    };
}

fn SentinelArray(comptime Underlying: type, options: RepeatOptions) type {
    return struct {
        const Self = @This();

        const capacity = if (options.max_count) |value|
            value
        else
            @compileError("You must specify the maximum count of expected items in the array.");

        pub const ResultType = [capacity:0]Underlying.ResultType;

        underlying: Underlying,

        fn parse(self: Self, input: *Input) anyerror!?ResultType {
            input.startParsing();
            var count: usize = 0;
            var items: ResultType = undefined;
            while (!options.isEnough(count)) {
                if (try self.underlying.parse(input)) |t| {
                    items[count] = t;
                    count += 1;
                } else {
                    break;
                }
            }
            if (count < options.min_count) {
                try input.reset();
                return null;
            } else {
                items[count] = 0;
                return items;
            }
        }

        fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<SentinelArray of {s} {any}>", .{ self.underlying, options });
        }
    };
}

fn RepeatTo(comptime Underlying: type, Collector: type, options: RepeatOptions) type {
    return struct {
        const Self = @This();

        pub const ResultType = Collector;

        underlying: Underlying,
        collector: Collector,
        addFn: *const fn (ctx: Collector, Underlying.ResultType) anyerror!void,

        fn parse(self: Self, input: *Input) anyerror!?ResultType {
            input.startParsing();
            var count: usize = 0;
            while (!options.isEnough(count)) {
                if (try self.underlying.parse(input)) |t| {
                    try self.addFn(self.collector, t);
                    count += 1;
                } else {
                    break;
                }
            }
            if (count < options.min_count) {
                try input.reset();
                return null;
            } else {
                return self.collector;
            }
        }

        fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<Collect {any} {any} to {any}>", .{ options, @typeName(Collector), self.underlying });
        }
    };
}

fn AndThen(comptime UnderlyingLeft: type, UnderlyingRight: type) type {
    return struct {
        const Self = @This();

        pub const ResultType = struct { UnderlyingLeft.ResultType, UnderlyingRight.ResultType };

        left: UnderlyingLeft,
        right: UnderlyingRight,

        fn parse(self: Self, input: *Input) anyerror!?ResultType {
            input.startParsing();
            if (try self.left.parse(input)) |l| {
                if (try self.right.parse(input)) |r| {
                    return .{ l, r };
                } else {
                    try input.reset();
                    return null;
                }
            } else {
                try input.reset();
                return null;
            }
        }

        fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<{any} andThen {any}>", .{ self.left, self.right });
        }
    };
}

fn LeftThen(comptime UnderlyingLeft: type, UnderlyingRight: type) type {
    return struct {
        const Self = @This();

        pub const ResultType = UnderlyingLeft.ResultType;

        underlying: AndThen(UnderlyingLeft, UnderlyingRight),

        fn parse(self: Self, input: *Input) anyerror!?ResultType {
            if (try self.underlying.parse(input)) |tp| {
                return tp[0];
            }
            return null;
        }

        fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<{any} leftThen {any}>", .{ self.left, self.right });
        }
    };
}

fn RightThen(comptime UnderlyingLeft: type, UnderlyingRight: type) type {
    return struct {
        const Self = @This();

        pub const ResultType = UnderlyingRight.ResultType;

        underlying: AndThen(UnderlyingLeft, UnderlyingRight),

        fn parse(self: Self, input: *Input) anyerror!?ResultType {
            if (try self.underlying.parse(input)) |tp| {
                return tp[1];
            }
            return null;
        }

        fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<{any} rightThen {any}>", .{ self.left, self.right });
        }
    };
}

fn OrElse(comptime UnderlyingLeft: type, UnderlyingRight: type) type {
    return struct {
        pub const ResultType = Either(UnderlyingLeft.ResultType, UnderlyingRight.ResultType);

        const Self = @This();

        left: UnderlyingLeft,
        right: UnderlyingRight,

        fn parse(self: Self, input: *Input) anyerror!?ResultType {
            input.startParsing();
            if (try self.left.parse(input)) |a| {
                return .{ .left = a };
            }
            try input.reset();
            if (try self.right.parse(input)) |b| {
                return .{ .right = b };
            }
            try input.reset();
            return null;
        }

        fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<{any} orElse {any}>", .{ self.left, self.right });
        }
    };
}

fn Tuple(comptime Underlyings: type) type {
    const struct_info: std.builtin.Type.Struct = switch (@typeInfo(Underlyings)) {
        .Struct => |s| s,
        else => @compileError(std.fmt.comptimePrint(
            "Parsers should be struct with parsers but it is {any}.",
            .{@typeInfo(Underlyings)},
        )),
    };

    return struct {
        const Self = @This();

        pub const ResultType = blk: {
            var types: [struct_info.fields.len]std.builtin.Type.StructField = undefined;
            for (struct_info.fields, 0..) |field, i| {
                types[i] = .{
                    .name = field.name,
                    .type = field.type.ResultType,
                    .default_value = null,
                    .is_comptime = false,
                    .alignment = 0,
                };
            }
            break :blk @Type(.{
                .Struct = .{
                    .layout = .auto,
                    .fields = &types,
                    .decls = &[_]std.builtin.Type.Declaration{},
                    .is_tuple = true,
                },
            });
        };
        const size = struct_info.fields.len;

        parsers: Underlyings,

        fn parse(self: Self, input: *Input) anyerror!?ResultType {
            input.startParsing();
            var result: ResultType = undefined;
            inline for (0..size) |i| {
                if (try self.parsers[i].parse(input)) |v| {
                    result[i] = v;
                } else {
                    try input.reset();
                    return null;
                }
            }
            return result;
        }

        fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<Tuple of {any}>", .{self.parsers});
        }
    };
}

fn OneCharOf(comptime chars: []const u8) type {
    return struct {
        pub const ResultType = u8;

        const Self = @This();

        const parser = AnyChar{};
        const sorted_chars: [chars.len]u8 = blk: {
            var buf: [chars.len]u8 = undefined;
            @memcpy(&buf, chars);
            std.mem.sort(u8, &buf, {}, lessThan);
            break :blk buf;
        };

        fn parse(_: Self, input: *Input) anyerror!?ResultType {
            input.startParsing();
            while (try parser.parse(input)) |ch| {
                if (std.sort.binarySearch(u8, ch, &sorted_chars, {}, compareChars)) |_| {
                    return ch;
                } else {
                    try input.reset();
                    return null;
                }
            }
            try input.reset();
            return null;
        }

        fn lessThan(_: void, lhs: u8, rhs: u8) bool {
            return lhs < rhs;
        }
        fn compareChars(_: void, lhs: u8, rhs: u8) std.math.Order {
            return std.math.order(lhs, rhs);
        }

        fn format(_: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<One char of \"{s}\">", .{chars});
        }
    };
}

fn Transform(comptime UnderlyingA: type, Context: type, B: type) type {
    return struct {
        pub const ResultType = B;

        const Self = @This();

        underlying: UnderlyingA,
        context: Context,
        transformFn: *const fn (ctx: Context, a: UnderlyingA.ResultType) anyerror!B,

        fn parse(self: Self, input: *Input) anyerror!?ResultType {
            input.startParsing();
            if (try self.underlying.parse(input)) |a| {
                return try self.transformFn(self.context, a);
            }
            try input.reset();
            return null;
        }

        fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<Transform result of the {any} to {any}>", .{ self.underlying, @typeName(B) });
        }
    };
}

fn Int(comptime T: type, max_buf_size: usize) type {
    return struct {
        pub const ResultType = T;

        const Self = @This();

        fn parse(_: Self, input: *Input) anyerror!?ResultType {
            input.startParsing();
            var buf: [max_buf_size]u8 = undefined;
            var idx: usize = 0;
            const sign = OneCharOf("+-"){};
            if (try sign.parse(input)) |sg| {
                buf[0] = sg;
                idx += 1;
            }
            const symbols = OneCharOf("0123456789_boXABCDF"){};
            while (try symbols.parse(input)) |s| : (idx += 1) {
                buf[idx] = s;
            }
            return std.fmt.parseInt(T, buf[0..idx], 0) catch {
                try input.reset();
                return null;
            };
        }

        fn format(_: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.writeAll("<Integer>");
        }
    };
}

fn Deffered(comptime Context: type, Type: type) type {
    return struct {
        const Self = @This();
        pub const ResultType = Type;

        context: Context,
        buildParserFn: *const fn (context: Context) anyerror!TaggedParser(Type),

        fn parse(self: Self, input: *Input) anyerror!?ResultType {
            const parser = try self.buildParserFn(self.context);
            defer parser.deinit();
            return try parser.parse(input);
        }

        fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<Deferred {any}>", .{self.buildParserFn});
        }
    };
}

fn Logged(comptime Underlying: type, scope: @Type(.EnumLiteral)) type {
    return struct {
        pub const ResultType = Underlying.ResultType;

        const Self = @This();

        const logger = std.log.scoped(scope);

        underlying: Underlying,

        fn parse(self: Self, input: *Input) anyerror!?ResultType {
            const maybe_result = self.underlying.parse(input) catch |err| {
                logger.debug("An error occured on parsing by {any} at {any}", .{ err, input });
                return err;
            };
            if (maybe_result) |result| {
                logger.debug("The result is {any} at {any}", .{ result, input });
                return result;
            } else {
                logger.debug("A parser failed at {any}", .{input});
                return null;
            }
        }

        fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<Logged with scope {s} {any}>", .{ @tagName(scope), self.underlying });
        }
    };
}

fn Coerce(comptime Underlying: type, ExpectedResultType: type) type {
    comptime {
        if (!std.meta.eql(@typeInfo(Underlying.ResultType), @typeInfo(ExpectedResultType))) {
            @compileError(std.fmt.comptimePrint(
                "Type {s} can't be cast to {s}",
                .{ @typeName(Underlying.ResultType), @typeName(ExpectedResultType) },
            ));
        }
    }
    return struct {
        pub const ResultType = ExpectedResultType;

        const Self = @This();

        underlying: Underlying,

        fn parse(self: Self, input: *Input) !?ResultType {
            if (try self.underlying.parse(input)) |v| {
                return @as(ExpectedResultType, v);
            } else {
                return null;
            }
        }
    };
}

fn Cut(comptime Underlying: type) type {
    return struct {
        pub const ResultType = Underlying.ResultType;

        const Self = @This();

        underlying: Underlying,

        fn parse(self: Self, input: *Input) !?ResultType {
            if (try self.underlying.parse(input)) |v| {
                input.cut();
                return v;
            } else {
                return null;
            }
        }
    };
}

test {
    std.testing.refAllDecls(@This());
}

test "more cases for int parser" {
    const p = int(i8);
    try std.testing.expectEqual(null, try p.parseString("+"));
    try std.testing.expectEqual(null, try p.parseString("+-2"));
    try std.testing.expectEqual(2, try p.parseString("0002"));
    try std.testing.expectEqual(2, try p.parseString("0_0_0_2"));
    try std.testing.expectEqual(2, try p.parseString("+0b10"));
    try std.testing.expectEqual(-2, try p.parseString("-0b10"));
}

test "parse a long sequence to slice" {
    // given:
    var sequence: [1024]u8 = undefined;
    for (0..sequence.len) |i| {
        sequence[i] = 'a';
    }
    const p = char('a').repeat(std.testing.allocator, .{});
    // when:
    const result = (try p.parseString(&sequence)).?;
    defer std.testing.allocator.free(result);
    // then:
    try std.testing.expectEqualSlices(u8, &sequence, result);
}
