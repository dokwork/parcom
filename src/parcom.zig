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
//! An implementation of the parser should follow this interface:
//! ```zig
//! struct {
//!     const Self = @This();
//!
//!     /// The type of the result when parsing is successful
//!     pub const ResultType: type;
//!
//!     /// Should get bytes from the reader and puts it to the buffer if they were
//!     /// not successfully parsed, or return the result of parsing.
//!     fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType
//! }
//! ```
const std = @import("std");

const log = std.log.scoped(.parcom);

/// Set of base parsers.
pub const Parsers = struct {
    /// Creates a parser that doesn't read any bytes from the input,
    /// and always returns passed value as the result.
    pub fn successfull(result: anytype) ParserCombinator(Successfull(@TypeOf(result))) {
        return .{ .underlying = .{ .result = result } };
    }

    /// Creates a parser that reads one byte from the input, and returns it as the result.
    pub inline fn anyChar() ParserCombinator(AnyChar) {
        return .{ .implementation = .{} };
    }

    test "Parse anyChar example" {
        try std.testing.expectEqual('a', try Parsers.anyChar().parseString(std.testing.allocator, "a"));
        try std.testing.expectEqual(null, try Parsers.anyChar().parseString(std.testing.allocator, ""));
    }

    /// Creates a parser that reads one byte from the input, and returns `C` as the
    /// result if the same byte was read.
    pub fn char(comptime C: u8) ParserCombinator(Const(AnyChar, C)) {
        return .{ .implementation = .{ .underlying = AnyChar{} } };
    }

    test "Parse char example" {
        const p = Parsers.char('a');
        try std.testing.expectEqual('a', try p.parseString(std.testing.allocator, "a"));
        try std.testing.expectEqual(null, try p.parseString(std.testing.allocator, "b"));
        try std.testing.expectEqual(null, try p.parseString(std.testing.allocator, ""));
    }

    /// Creates a parser that reads one byte from the input and returns it as the result
    /// if it is present in the chars set.
    pub inline fn oneCharOf(comptime chars: []const u8) ParserCombinator(OneCharOf(chars)) {
        return .{ .implementation = .{} };
    }

    test "Parse one of chars" {
        const p = Parsers.oneCharOf("ab");

        try std.testing.expectEqual('a', try p.parseString(std.testing.allocator, "a"));
        try std.testing.expectEqual('b', try p.parseString(std.testing.allocator, "b"));
        try std.testing.expectEqual(null, try p.parseString(std.testing.allocator, "c"));
    }

    /// Creates a parser that reads bytes from the input into the buffer as long as they
    /// are in the chars set "+-0123456789_boXABCDF". Then it attempts to parse
    /// the buffer as an integer using `std.fmt.parseInt`.
    pub inline fn int(comptime T: type) ParserCombinator(Int(T, 128)) {
        return .{ .implementation = .{} };
    }

    test "Parse int example" {
        const p = Parsers.int(i8);
        const alloc = std.testing.allocator;
        try std.testing.expectEqual(2, try p.parseString(alloc, "2"));
        try std.testing.expectEqual(2, try p.parseString(alloc, "+2"));
        try std.testing.expectEqual(-2, try p.parseString(alloc, "-2"));
        try std.testing.expectEqual(null, try p.parseString(alloc, "+"));
        try std.testing.expectEqual(null, try p.parseString(alloc, "+-2"));
        try std.testing.expectEqual(2, try p.parseString(alloc, "0002"));
        try std.testing.expectEqual(2, try p.parseString(alloc, "0_0_0_2"));
        try std.testing.expectEqual(2, try p.parseString(alloc, "0b10"));
        try std.testing.expectEqual(2, try p.parseString(alloc, "+0b10"));
        try std.testing.expectEqual(-2, try p.parseString(alloc, "-0b10"));
        try std.testing.expectEqual(8, try p.parseString(alloc, "0o10"));
        try std.testing.expectEqual(10, try p.parseString(alloc, "0XA"));
    }

    /// Creates a parser that processes a char from the chars set ['a'..'z', 'A'..'Z', '0'..'9'].
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

    test "letterOrNumber example" {
        const p = Parsers.letterOrNumber();
        try std.testing.expectEqual('b', try p.parseString(std.testing.allocator, "b"));
        try std.testing.expectEqual('A', try p.parseString(std.testing.allocator, "A"));
        try std.testing.expectEqual('1', try p.parseString(std.testing.allocator, "1"));
        try std.testing.expectEqual(null, try p.parseString(std.testing.allocator, "-"));
    }

    /// Creates a parser that processes only passed sequence of chars.
    pub inline fn word(comptime W: []const u8) ParserCombinator(Conditional(WordLabel(W), Array(AnyChar, W.len), []const u8)) {
        return .{
            .implementation = .{
                .underlying = Array(AnyChar, W.len){ .underlying = AnyChar{} },
                .context = W,
                .conditionFn = struct {
                    fn compareWords(expected: []const u8, parsed: [W.len]u8) bool {
                        return std.mem.eql(u8, expected, &parsed);
                    }
                }.compareWords,
            },
        };
    }

    test "Parse word example" {
        try std.testing.expectEqualStrings("foo", &((try word("foo").parseString(std.testing.allocator, "foo")).?));
    }

    /// Creates a parser that processes characters within the ASCII range, where From is the lowest
    /// character in the ASCII table and To is the highest, inclusive.
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

    test "Parse range example" {
        const p = Parsers.range('A', 'C');
        try std.testing.expectEqual(null, try p.parseString(std.testing.allocator, "a"));
        try std.testing.expectEqual(null, try p.parseString(std.testing.allocator, "b"));
        try std.testing.expectEqual(null, try p.parseString(std.testing.allocator, "c"));
        try std.testing.expectEqual(null, try p.parseString(std.testing.allocator, "D"));
        try std.testing.expectEqual('A', try p.parseString(std.testing.allocator, "A"));
        try std.testing.expectEqual('B', try p.parseString(std.testing.allocator, "B"));
        try std.testing.expectEqual('C', try p.parseString(std.testing.allocator, "C"));
    }

    pub inline fn tuple(parsers: anytype) ParserCombinator(Tuple(@TypeOf(parsers))) {
        return .{ .implementation = .{ .parsers = parsers } };
    }

    test "Parse tuple example" {
        const p = Parsers.tuple(.{ Parsers.char('a'), Parsers.char('b'), Parsers.char('c') });
        try std.testing.expectEqual(.{ 'a', 'b', 'c' }, (try p.parseString(std.testing.allocator, "abcdef")).?);
    }

    /// Creates a parser that invoke the function `f` to create a tagged parser, which will be used
    /// to parse the input. That tagged parser will be deinited at the end of parsing.
    pub inline fn lazy(
        comptime ResultType: type,
        context: anytype,
        f: *const fn (context: @TypeOf(context)) anyerror!TaggedParser(ResultType),
    ) ParserCombinator(Lazy(@TypeOf(context), ResultType)) {
        return .{
            .implementation = Lazy(@TypeOf(context), ResultType){ .context = context, .buildParserFn = f },
        };
    }

    // TODO: provide an example of using LazyParser
};

/// The final version of the parser with tagged result type.
/// This version of the parser can be useful when the type of the
/// parser should be provided manually, as example, in the function signature.
pub fn TaggedParser(comptime TaggedType: type) type {
    return struct {
        pub const ResultType = TaggedType;

        const Self = @This();

        alloc: std.mem.Allocator,
        underlying: *const anyopaque,
        parseFn: *const fn (parser: *const anyopaque, cursor: *Cursor) anyerror!?ResultType,
        deinitFn: *const fn (alloc: std.mem.Allocator, underlying: *const anyopaque) void,

        inline fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            return try self.parseFn(self.underlying, cursor);
        }

        /// Deallocates memory with underlying parser.
        pub fn deinit(self: Self) void {
            self.deinitFn(self.alloc, self.underlying);
        }

        fn parseAnyReader(self: Self, alloc: std.mem.Allocator, reader: std.io.AnyReader) !?ResultType {
            var cursor = Cursor.init(alloc, reader);
            defer cursor.deinit();
            return try self.parse(&cursor);
        }

        /// This method is similar to the same method in `ParserCombinator`.
        pub inline fn parseReader(self: Self, alloc: std.mem.Allocator, reader: anytype) !?ResultType {
            return try self.parseAnyReader(alloc, reader.any());
        }

        /// This method is similar to the same method in `ParserCombinator`.
        pub inline fn parseString(
            self: Self,
            alloc: std.mem.Allocator,
            str: []const u8,
        ) !?ResultType {
            var fbs = std.io.fixedBufferStream(str);
            return self.parseReader(alloc, fbs.reader());
        }
    };
}

/// The wrapper around an implementation of a parser. It provides methods
/// to combine parsers to build a new one.
pub fn ParserCombinator(comptime Implementation: type) type {
    return struct {
        pub const ResultType = Implementation.ResultType;

        const Self = @This();

        /// The underlying implementation of the parser
        implementation: Implementation,

        pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("{any}", .{self.implementation});
        }

        /// Allocates memory for underlying implementation by the `alloc`,
        /// and copies underlying parser to that memory. It makes possible to erase the type of the
        /// underlying parser. The `deinit` method of the returned TaggedParser should be invoked
        /// to free allocated memory.
        pub fn tagged(self: Self, alloc: std.mem.Allocator) !TaggedParser(ResultType) {
            const fns = struct {
                fn parse(ptr: *const anyopaque, cursor: *Cursor) anyerror!?ResultType {
                    const implementation: *const Implementation = @ptrCast(@alignCast(ptr));
                    return try implementation.parse(cursor);
                }
                fn deinit(allocator: std.mem.Allocator, ptr: *const anyopaque) void {
                    const implementation: *const Implementation = @ptrCast(@alignCast(ptr));
                    allocator.destroy(implementation);
                }
            };
            const on_heap = try alloc.create(Implementation);
            on_heap.* = self.implementation;
            return .{
                .alloc = alloc,
                .underlying = on_heap,
                .parseFn = fns.parse,
                .deinitFn = fns.deinit,
            };
        }

        test "tagged parser example" {
            const p = Parsers.char('a');
            const tg: TaggedParser(u8) = try p.tagged(std.testing.allocator);
            defer tg.deinit();

            try std.testing.expectEqual('a', try tg.parseString(std.testing.allocator, "a"));
        }

        inline fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            return try self.implementation.parse(cursor);
        }

        fn parseAnyReader(self: Self, alloc: std.mem.Allocator, reader: std.io.AnyReader) !?ResultType {
            var cursor = Cursor.init(alloc, reader);
            defer cursor.deinit();
            return try self.parse(&cursor);
        }

        /// It runs this parser to parse an input from the `reader`. The whole input
        /// will be persisted in the inner buffer during the parsing. The allocator is
        /// used to allocate memory for the inner buffer.
        pub inline fn parseReader(self: Self, alloc: std.mem.Allocator, reader: anytype) !?ResultType {
            return try self.parseAnyReader(alloc, reader.any());
        }

        /// It creates an fixed buffer stream from the passed string to build the
        /// reader, and then invokes the `parse` method with it reader.
        pub inline fn parseString(
            self: Self,
            alloc: std.mem.Allocator,
            str: []const u8,
        ) !?ResultType {
            var fbs = std.io.fixedBufferStream(str);
            return self.parseReader(alloc, fbs.reader());
        }

        pub inline fn andThen(
            self: Self,
            other: anytype,
        ) ParserCombinator(AndThen(Implementation, @TypeOf(other.implementation))) {
            return .{ .implementation = .{ .left = self.implementation, .right = other.implementation } };
        }

        test "andThen example" {
            const p = Parsers.char('a').andThen(Parsers.char('b'));
            try std.testing.expectEqual(null, try p.parseString(std.testing.allocator, "aa"));
            try std.testing.expectEqual(null, try p.parseString(std.testing.allocator, "bb"));
            try std.testing.expectEqual(.{ 'a', 'b' }, try p.parseString(std.testing.allocator, "ab"));
        }

        pub inline fn orElse(
            self: Self,
            right: anytype,
        ) ParserCombinator(OrElse(Implementation, @TypeOf(right.implementation))) {
            return .{ .implementation = .{ .left = self.implementation, .right = right.implementation } };
        }

        test "orElse example" {
            const p = Parsers.char('a').orElse(Parsers.char('b'));

            try std.testing.expectEqual(Either(u8, u8){ .left = 'a' }, try p.parseString(std.testing.allocator, "a"));
            try std.testing.expectEqual(Either(u8, u8){ .right = 'b' }, try p.parseString(std.testing.allocator, "b"));
            try std.testing.expectEqual(null, try p.parseString(std.testing.allocator, "c"));
        }

        pub fn optional(self: Self) ParserCombinator(OrElse(Implementation, Successfull(void))) {
            return .{
                .implementation = OrElse(Implementation, Successfull(void)){
                    .left = self.implementation,
                    .right = Successfull(void){ .result = {} },
                },
            };
        }

        test "optional example" {
            const p = Parsers.char('a').optional();
            try std.testing.expectEqual(Either(u8, void){ .left = 'a' }, p.parseString(std.testing.allocator, "a"));
            try std.testing.expectEqual(Either(u8, void){ .right = {} }, p.parseString(std.testing.allocator, "b"));
        }

        pub inline fn suchThat(
            self: Self,
            context: anytype,
            condition: *const fn (ctx: @TypeOf(context), value: @TypeOf(self).ResultType) bool,
        ) ParserCombinator(Conditional("Such that", @TypeOf(self), @TypeOf(context))) {
            return .{ .implementation = .{ .underlying = self.implementation, .context = context, .conditionFn = condition } };
        }

        pub inline fn repeat(self: Self, alloc: std.mem.Allocator) ParserCombinator(Slice(Implementation)) {
            return .{ .implementation = .{ .underlying = self.implementation, .alloc = alloc } };
        }

        test "repeat example" {
            var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
            defer arena.deinit();
            const alloc = arena.allocator();

            const p = Parsers.char('a').repeat(alloc);

            try std.testing.expectEqualSlices(u8, &[_]u8{}, (try p.parseString(alloc, "")).?);
            try std.testing.expectEqualSlices(u8, &[_]u8{'a'}, (try p.parseString(alloc, "a")).?);
            try std.testing.expectEqualSlices(u8, &[_]u8{ 'a', 'a' }, (try p.parseString(alloc, "aa")).?);
            try std.testing.expectEqualSlices(u8, &[_]u8{ 'a', 'a' }, (try p.parseString(alloc, "aab")).?);
        }

        pub inline fn repeatToArray(self: Self, comptime count: u8) ParserCombinator(Array(Implementation, count)) {
            return .{ .implementation = .{ .underlying = self.implementation } };
        }

        test "repeatToArray example" {
            const p = Parsers.char('a').repeatToArray(2);

            try std.testing.expectEqual(null, try p.parseString(std.testing.allocator, ""));
            try std.testing.expectEqual(null, try p.parseString(std.testing.allocator, "ab"));
            try std.testing.expectEqualSlices(
                u8,
                &[_]u8{ 'a', 'a' },
                &((try p.parseString(std.testing.allocator, "aa")).?),
            );
            try std.testing.expectEqualSlices(
                u8,
                &[_]u8{ 'a', 'a' },
                &((try p.parseString(std.testing.allocator, "aaa")).?),
            );
        }

        pub inline fn repeatToSentinelArray(
            self: Self,
            comptime min_count: u8,
            comptime max_count: u8,
        ) ParserCombinator(SentinelArray(Implementation, min_count, max_count)) {
            // because of https://github.com/ziglang/zig/pull/21509
            const info = @typeInfo(ResultType);
            switch (info) {
                .Int => {},
                else => @compileError("Repeating to sentinel array is possible only for numbers"),
            }
            return .{ .implementation = .{ .underlying = self.implementation } };
        }

        test "repeatToSentinelArray example" {
            const p0 = Parsers.char('a').repeatToSentinelArray(0, 2);

            var result: [2:0]u8 = (try p0.parseString(std.testing.allocator, "")).?;
            try std.testing.expectEqual(0, result[0]);

            const p = Parsers.char('a').repeatToSentinelArray(1, 2);
            try std.testing.expectEqual(null, try p.parseString(std.testing.allocator, ""));

            result = (try p.parseString(std.testing.allocator, "ab")).?;
            try std.testing.expectEqual('a', result[0]);
            try std.testing.expectEqual(0, result[2]);

            result = (try p.parseString(std.testing.allocator, "aa")).?;
            try std.testing.expectEqual('a', result[0]);
            try std.testing.expectEqual('a', result[1]);
            try std.testing.expectEqual(0, result[2]);
        }

        pub inline fn collectTo(
            self: Self,
            comptime Collector: type,
            collector: *Collector,
            addFn: *const fn (ctx: *Collector, ResultType) anyerror!void,
        ) ParserCombinator(Collect(Implementation, Collector)) {
            return .{ .implementation = .{ .underlying = self.implementation, .collector = collector, .addFn = addFn } };
        }

        pub inline fn transform(
            self: Self,
            comptime Result: type,
            context: anytype,
            f: *const fn (ctx: @TypeOf(context), a: ResultType) anyerror!Result,
        ) ParserCombinator(Transform(Implementation, @TypeOf(context), Result)) {
            return .{ .implementation = .{ .underlying = self.implementation, .context = context, .transformFn = f } };
        }

        test "transform example" {
            const p = Parsers.anyChar().repeatToArray(2).transform(u8, {}, struct {
                fn parseInt(_: void, arr: [2]u8) anyerror!u8 {
                    return try std.fmt.parseInt(u8, &arr, 10);
                }
            }.parseInt);

            try std.testing.expectEqual(42, try p.parseString(std.testing.allocator, "42"));
        }

        /// Create a parser that writes to the log with passed scope and debug level
        /// the result of running the underlying parser.
        pub fn debug(self: Self, comptime scope: @Type(.EnumLiteral)) ParserCombinator(Logged(Self, scope)) {
            return .{ .implementation = Logged(Self, scope){ .underlying = self } };
        }
    };
}

/// Alias for `union(enum) { left: A, right: B }`
pub fn Either(comptime A: type, B: type) type {
    return union(enum) { left: A, right: B };
}

/// Keeps buffer of the read parsed bytes, and the index of the last not parsed element in it.
/// Note, the buffer will contain whole input in successful case.
const Cursor = struct {
    // TODO: make it possible to limit the maximum size of this buffer
    buffer: std.ArrayList(u8),
    reader: std.io.AnyReader,
    idx: usize = 0,

    fn init(alloc: std.mem.Allocator, reader: std.io.AnyReader) Cursor {
        return .{ .buffer = std.ArrayList(u8).init(alloc), .reader = reader };
    }

    fn deinit(self: Cursor) void {
        self.buffer.deinit();
    }

    pub fn format(self: Cursor, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        if (self.idx < self.buffer.items.len) {
            const left_bound = if (self.idx == 0) 0 else @min(self.idx - 1, self.buffer.items.len);
            const right_bound = @min(self.idx + 1, self.buffer.items.len);
            const symbol = switch (self.buffer.items[self.idx]) {
                '\n' => "\\n",
                '\r' => "\\r",
                '\t' => "\\t",
                else => &[_]u8{self.buffer.items[self.idx]},
            };
            try writer.print(
                "position {d}:\n{s}[{s}]{s}",
                .{
                    self.idx,
                    self.buffer.items[0..left_bound],
                    symbol,
                    self.buffer.items[right_bound..],
                },
            );
        } else {
            try writer.print(
                "position {d}:\n{s}[]",
                .{ self.idx, self.buffer.items },
            );
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
        pub fn parse(self: @This(), _: *Cursor) anyerror!?ResultType {
            return self.result;
        }
    };
}

fn Failed(comptime T: type) type {
    return struct {
        pub const ResultType = T;
        pub fn parse(_: @This(), _: *Cursor) anyerror!?ResultType {
            return null;
        }
    };
}

const AnyChar = struct {
    pub const ResultType = u8;

    pub fn parse(_: AnyChar, cursor: *Cursor) anyerror!?u8 {
        if (cursor.idx < cursor.buffer.items.len and cursor.buffer.items[cursor.idx..].len > 0) {
            cursor.idx += 1;
            return cursor.buffer.items[cursor.idx - 1];
        } else {
            const v = cursor.reader.readByte() catch |err| {
                switch (err) {
                    error.EndOfStream => return null,
                    else => return err,
                }
            };
            try cursor.buffer.append(v);
            cursor.idx += 1;
            return v;
        }
    }

    pub fn format(_: AnyChar, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
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

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            const orig_idx = cursor.idx;
            if (try self.underlying.parse(cursor)) |res| {
                if (self.conditionFn(self.context, res)) return res;
            }
            cursor.idx = orig_idx;
            return null;
        }

        pub fn format(_: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.writeAll(std.fmt.comptimePrint("<{s}>", .{Label}));
        }
    };
}

fn Const(comptime Underlying: type, comptime template: Underlying.ResultType) type {
    return struct {
        const Self = @This();

        pub const ResultType = Underlying.ResultType;

        underlying: Underlying,

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            const orig_idx = cursor.idx;
            if (try self.underlying.parse(cursor)) |res| {
                if (res == template) return res;
            }
            cursor.idx = orig_idx;
            return null;
        }

        pub fn format(_: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.writeAll(std.fmt.comptimePrint("<Constant {any}>", .{template}));
        }
    };
}

fn Slice(comptime Underlying: type) type {
    return struct {
        const Self = @This();

        pub const ResultType = []Underlying.ResultType;

        underlying: Underlying,
        alloc: std.mem.Allocator,

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            var buffer: ResultType = try self.alloc.alloc(Underlying.ResultType, 5);
            var i: usize = 0;
            while (try self.underlying.parse(cursor)) |t| : (i += 1) {
                if (i == buffer.len) {
                    buffer = try self.alloc.realloc(buffer, newSize(buffer.len));
                }
                buffer[i] = t;
            }
            return try self.alloc.realloc(buffer, i);
        }

        pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<Slice of {s}>", .{self.underlying});
        }

        inline fn newSize(current_len: usize) usize {
            return current_len * 17 / 10;
        }
    };
}

fn Array(comptime Underlying: type, count: u8) type {
    return struct {
        const Self = @This();

        pub const ResultType = [count]Underlying.ResultType;

        underlying: Underlying,

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            const orig_idx = cursor.idx;
            var result: ResultType = undefined;
            for (0..count) |i| {
                if (try self.underlying.parse(cursor)) |t| {
                    result[i] = t;
                } else {
                    cursor.idx = orig_idx;
                    return null;
                }
            }
            return result;
        }

        pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<Array of {s}>", .{self.underlying});
        }
    };
}

fn SentinelArray(comptime Underlying: type, min_count: u8, max_count: u8) type {
    std.debug.assert(max_count > 0);
    return struct {
        const Self = @This();

        pub const ResultType = [max_count:0]Underlying.ResultType;

        underlying: Underlying,

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            const orig_idx = cursor.idx;
            var result: ResultType = undefined;
            var i: usize = 0;
            while (i < max_count) : (i += 1) {
                if (try self.underlying.parse(cursor)) |t| {
                    result[i] = t;
                } else {
                    break;
                }
            }
            if (i < min_count) {
                cursor.idx = orig_idx;
                return null;
            }
            result[i] = 0;
            return result;
        }

        pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<SentinelArray of {s}>", .{self.underlying});
        }
    };
}

fn Collect(comptime Underlying: type, Collector: type) type {
    return struct {
        const Self = @This();

        pub const ResultType = *Collector;

        underlying: Underlying,
        collector: *Collector,
        addFn: *const fn (ctx: *Collector, Underlying.ResultType) anyerror!void,

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            while (try self.underlying.parse(cursor)) |t| {
                try self.addFn(self.collector, t);
            }
            return self.collector;
        }

        pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<Collect {any} to {any}>", .{ @typeName(Collector), self.underlying });
        }
    };
}

fn AndThen(comptime UnderlyingLeft: type, UnderlyingRight: type) type {
    return struct {
        const Self = @This();

        pub const ResultType = struct { UnderlyingLeft.ResultType, UnderlyingRight.ResultType };

        left: UnderlyingLeft,
        right: UnderlyingRight,

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            const orig_idx = cursor.idx;
            if (try self.left.parse(cursor)) |l| {
                if (try self.right.parse(cursor)) |r| {
                    return .{ l, r };
                } else {
                    cursor.idx = orig_idx;
                    return null;
                }
            } else {
                cursor.idx = orig_idx;
                return null;
            }
        }

        pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<{any} andThen {any}>", .{ self.left, self.right });
        }
    };
}

fn OrElse(comptime UnderlyingLeft: type, UnderlyingRight: type) type {
    return struct {
        pub const ResultType = Either(UnderlyingLeft.ResultType, UnderlyingRight.ResultType);

        const Self = @This();

        left: UnderlyingLeft,
        right: UnderlyingRight,

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            const orig_idx = cursor.idx;
            if (try self.left.parse(cursor)) |a| {
                return .{ .left = a };
            }
            cursor.idx = orig_idx;
            if (try self.right.parse(cursor)) |b| {
                return .{ .right = b };
            }
            cursor.idx = orig_idx;
            return null;
        }

        pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
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

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            const orig_idx = cursor.idx;
            var result: ResultType = undefined;
            inline for (0..size) |i| {
                if (try self.parsers[i].parse(cursor)) |v| {
                    result[i] = v;
                } else {
                    cursor.idx = orig_idx;
                    return null;
                }
            }
            return result;
        }

        pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
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

        fn parse(_: Self, cursor: *Cursor) anyerror!?ResultType {
            const orig_idx = cursor.idx;
            while (try parser.parse(cursor)) |ch| {
                if (std.sort.binarySearch(u8, ch, &sorted_chars, {}, compareChars)) |_| {
                    return ch;
                } else {
                    cursor.idx = orig_idx;
                    return null;
                }
            }
            cursor.idx = orig_idx;
            return null;
        }

        fn lessThan(_: void, lhs: u8, rhs: u8) bool {
            return lhs < rhs;
        }
        fn compareChars(_: void, lhs: u8, rhs: u8) std.math.Order {
            return std.math.order(lhs, rhs);
        }

        pub fn format(_: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
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

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            const orig_idx = cursor.idx;
            if (try self.underlying.parse(cursor)) |a| {
                return try self.transformFn(self.context, a);
            }
            cursor.idx = orig_idx;
            return null;
        }

        pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<Transform result of the {any} to {any}>", .{ self.underlying, @typeName(B) });
        }
    };
}

fn Int(comptime T: type, max_buf_size: usize) type {
    return struct {
        pub const ResultType = T;

        const Self = @This();

        fn parse(_: Self, cursor: *Cursor) anyerror!?ResultType {
            const orig_idx = cursor.idx;
            var buf: [max_buf_size]u8 = undefined;
            var idx: usize = 0;
            const symbols = OneCharOf("+-0123456789_boXABCDF"){};
            while (try symbols.parse(cursor)) |s| : (idx += 1) {
                buf[idx] = s;
            }
            return std.fmt.parseInt(T, buf[0..idx], 0) catch {
                cursor.idx = orig_idx;
                return null;
            };
        }

        pub fn format(_: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.writeAll("<Integer>");
        }
    };
}

fn Lazy(comptime Context: type, Type: type) type {
    return struct {
        const Self = @This();
        pub const ResultType = Type;

        context: Context,
        buildParserFn: *const fn (context: Context) anyerror!TaggedParser(Type),

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            const parser = try self.buildParserFn(self.context);
            defer parser.deinit();
            return try parser.parse(cursor);
        }

        pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<Lazy {any}>", .{self.buildParserFn});
        }
    };
}

fn Logged(comptime Underlying: type, scope: @Type(.EnumLiteral)) type {
    return struct {
        pub const ResultType = Underlying.ResultType;

        const Self = @This();

        const logger = std.log.scoped(scope);

        underlying: Underlying,

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            const maybe_result = self.underlying.parse(cursor) catch |err| {
                logger.debug("An error occured on parsing by {any} at {any}", .{ err, cursor });
                return err;
            };
            if (maybe_result) |result| {
                logger.debug("The result is {any} at {any}", .{ result, cursor });
                return result;
            } else {
                logger.debug("A parser failed at {any}", .{cursor});
                return null;
            }
        }

        pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<Logged with scope {s} {any}>", .{ @tagName(scope), self.underlying });
        }
    };
}

test {
    std.testing.refAllDecls(@This());
}
