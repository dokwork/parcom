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

//! This is the simple library provided an implementation of the parser combinators.
const std = @import("std");

const log = std.log.scoped(.parsec);

/// Keeps buffer of the read parsed bytes, and index of the last not parsed
/// element in it.
const Cursor = struct {
    buffer: std.ArrayList(u8),
    reader: std.io.AnyReader,
    idx: usize = 0,

    pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        if (self.idx < self.buffer.items.len) {
            const left_bound = if (self.idx == 0) 0 else @min(self.idx - 1, self.buffer.items.len);
            const right_bound = @min(self.idx + 1, self.buffer.items.len);
            const symbol = switch (self.buffer.items[self.idx]) {
                '\n' => "\\n",
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

/// It runs the `parser` to parse an input from the `reader`. The whole input
/// will be persisted in the inner buffer during the parsing. The allocator is
/// used to allocate memory for inner buffer.
pub fn parse(alloc: std.mem.Allocator, parser: anytype, reader: anytype) !?@TypeOf(parser).ResultType {
    var cursor = Cursor{ .buffer = std.ArrayList(u8).init(alloc), .reader = reader.any() };
    defer cursor.buffer.deinit();
    return try parser.parse(&cursor);
}

/// It creates an fixed buffer stream from the passed string to build the
/// reader, and then invokes the `parse` method with it reader.
pub inline fn parseStr(alloc: std.mem.Allocator, parser: anytype, str: []const u8) !?@TypeOf(parser).ResultType {
    var fbs = std.io.fixedBufferStream(str);
    return parse(alloc, parser, fbs.reader());
}

pub fn successfull(result: anytype) Successfull(@TypeOf(result)) {
    return .{ .result = result };
}

fn Successfull(comptime T: type) type {
    return struct {
        pub const ResultType = T;
        const Self = @This();

        result: ResultType,

        pub fn parse(self: Self, _: *Cursor) anyerror!?ResultType {
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

pub inline fn anyChar() AnyCharParser {
    return AnyCharParser{};
}

const AnyCharParser = struct {
    pub const ResultType = u8;

    pub fn parse(_: AnyCharParser, cursor: *Cursor) anyerror!?u8 {
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

    pub fn format(_: AnyCharParser, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        try writer.writeAll("<any char>");
    }
};

test "Parse AnyChar" {
    try std.testing.expectEqual(null, try parseStr(std.testing.allocator, anyChar(), ""));
    try std.testing.expectEqual('a', try parseStr(std.testing.allocator, anyChar(), "a"));
}

pub inline fn conditional(
    comptime Label: []const u8,
    parser: anytype,
    context: anytype,
    condition: *const fn (ctx: @TypeOf(context), value: @TypeOf(parser).ResultType) bool,
) ConditionalParser(Label, @TypeOf(parser), @TypeOf(context)) {
    return .{ .underlying = parser, .context = context, .conditionFn = condition };
}

fn ConditionalParser(comptime Label: []const u8, Underlying: type, Context: type) type {
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
                log.debug("The value {any} is not satisfied to the condition.", .{res});
            }
            log.debug(
                "Parser {any} was failed at {any}",
                .{ self.underlying, cursor },
            );
            cursor.idx = orig_idx;
            return null;
        }

        pub fn format(_: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.writeAll(std.fmt.comptimePrint("<{s}>", .{Label}));
        }
    };
}

pub inline fn word(comptime W: []const u8) ConditionalParser(labelWord(W), ArrayParser(AnyCharParser, W.len), []const u8) {
    return conditional(labelWord(W), array(anyChar(), W.len), W, struct {
        fn compareWords(expected: []const u8, parsed: [W.len]u8) bool {
            return std.mem.eql(u8, expected, &parsed);
        }
    }.compareWords);
}
fn labelWord(comptime w: []const u8) *const [std.fmt.comptimePrint("Word {any}", .{w}).len:0]u8 {
    return std.fmt.comptimePrint("Word {any}", .{w});
}

test "Parse constant word" {
    try std.testing.expectEqualStrings("foo", &((try parseStr(std.testing.allocator, word("foo"), "foo")).?));
}

pub inline fn range(comptime From: u8, To: u8) ConditionalParser(labelRange(From, To), AnyCharParser, void) {
    comptime {
        std.debug.assert(From < To);
    }
    return conditional(labelRange(From, To), anyChar(), {}, struct {
        fn isInRange(_: void, value: u8) bool {
            return From <= value and value <= To;
        }
    }.isInRange);
}
fn labelRange(
    comptime From: u8,
    To: u8,
) *const [std.fmt.comptimePrint("Range of char from {c} to {c}", .{ From, To }).len:0]u8 {
    return std.fmt.comptimePrint("Range of char from {c} to {c}", .{ From, To });
}

test "Parse char in range" {
    const p = range('A', 'C');
    try std.testing.expectEqual(null, try parseStr(std.testing.allocator, p, "a"));
    try std.testing.expectEqual(null, try parseStr(std.testing.allocator, p, "b"));
    try std.testing.expectEqual(null, try parseStr(std.testing.allocator, p, "c"));
    try std.testing.expectEqual(null, try parseStr(std.testing.allocator, p, "D"));
    try std.testing.expectEqual('A', try parseStr(std.testing.allocator, p, "A"));
    try std.testing.expectEqual('B', try parseStr(std.testing.allocator, p, "B"));
    try std.testing.expectEqual('C', try parseStr(std.testing.allocator, p, "C"));
}

pub inline fn letterOrNumber() ConditionalParser("Letter or number", AnyCharParser, void) {
    return conditional("Letter or number", anyChar(), {}, struct {
        fn isLetterOrNumber(_: void, value: u8) bool {
            return switch (value) {
                'a'...'z' => true,
                'A'...'Z' => true,
                '0'...'9' => true,
                else => false,
            };
        }
    }.isLetterOrNumber);
}

test "Parse letters and numbers" {
    const p = letterOrNumber();
    try std.testing.expectEqual('b', try parseStr(std.testing.allocator, p, "b"));
    try std.testing.expectEqual('A', try parseStr(std.testing.allocator, p, "A"));
    try std.testing.expectEqual('1', try parseStr(std.testing.allocator, p, "1"));
    try std.testing.expectEqual(null, try parseStr(std.testing.allocator, p, "-"));
}

pub inline fn constant(
    parser: anytype,
    comptime template: @TypeOf(parser).ResultType,
) ConstParser(@TypeOf(parser), template) {
    return .{ .underlying = parser };
}

fn ConstParser(comptime Underlying: type, comptime template: Underlying.ResultType) type {
    return struct {
        const Self = @This();

        pub const ResultType = Underlying.ResultType;

        underlying: Underlying,

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            const orig_idx = cursor.idx;
            if (try self.underlying.parse(cursor)) |res| {
                if (res == template) return res;
                log.debug(
                    "{any} is not equal to {any} at {any}",
                    .{ res, template, cursor },
                );
            }
            cursor.idx = orig_idx;
            return null;
        }

        pub fn format(_: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.writeAll(std.fmt.comptimePrint("<Constant {any}>", .{template}));
        }
    };
}

pub fn char(comptime C: u8) ConstParser(AnyCharParser, C) {
    return constant(anyChar(), C);
}

test "Parse constant char" {
    try std.testing.expectEqual(null, try parseStr(std.testing.allocator, char('a'), ""));
    try std.testing.expectEqual(null, try parseStr(std.testing.allocator, char('a'), "b"));
    try std.testing.expectEqual('a', try parseStr(std.testing.allocator, char('a'), "a"));
}

pub inline fn slice(parser: anytype, buffer: []u8) SliceParser(@TypeOf(parser)) {
    return .{ .underlying = parser, .buffer = buffer };
}

fn SliceParser(comptime Underlying: type) type {
    return struct {
        const Self = @This();

        pub const ResultType = []Underlying.ResultType;

        underlying: Underlying,
        buffer: []u8,

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            var i: usize = 0;
            while (try self.underlying.parse(cursor)) |t| : (i += 1) {
                self.buffer[i] = t;
            }
            return self.buffer[0..i];
        }

        pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<slice of {s}>", .{self.underlying});
        }
    };
}

test "Parse slice of chars" {
    var buf: [5]u8 = undefined;
    const p = slice(char('a'), &buf);

    try std.testing.expectEqualSlices(u8, &[_]u8{}, (try parseStr(std.testing.allocator, p, "")).?);
    try std.testing.expectEqualSlices(u8, &[_]u8{'a'}, (try parseStr(std.testing.allocator, p, "a")).?);
    try std.testing.expectEqualSlices(u8, &[_]u8{ 'a', 'a' }, (try parseStr(std.testing.allocator, p, "aa")).?);
    try std.testing.expectEqualSlices(u8, &[_]u8{ 'a', 'a' }, (try parseStr(std.testing.allocator, p, "aab")).?);
}

pub inline fn array(parser: anytype, comptime count: u8) ArrayParser(@TypeOf(parser), count) {
    return .{ .underlying = parser };
}

fn ArrayParser(comptime Underlying: type, count: u8) type {
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
                    log.debug(
                        "Parser {any} was failed at {any}",
                        .{ self.underlying, cursor },
                    );
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

test "Parse array of chars" {
    const p = array(char('a'), 2);

    try std.testing.expectEqual(null, try parseStr(std.testing.allocator, p, ""));
    try std.testing.expectEqual(null, try parseStr(std.testing.allocator, p, "ab"));
    try std.testing.expectEqualSlices(u8, &[_]u8{ 'a', 'a' }, &((try parseStr(std.testing.allocator, p, "aa")).?));
    try std.testing.expectEqualSlices(u8, &[_]u8{ 'a', 'a' }, &((try parseStr(std.testing.allocator, p, "aaa")).?));
}

pub inline fn collect(
    comptime Collector: type,
    parser: anytype,
    collector: *Collector,
    append: *const fn (ctx: *Collector, @TypeOf(parser).ResultType) anyerror!void,
) CollectorParser(@TypeOf(parser), Collector) {
    return .{ .underlying = parser, .collector = collector, .appendFn = append };
}

fn CollectorParser(comptime Underlying: type, Collector: type) type {
    return struct {
        const Self = @This();

        pub const ResultType = *Collector;

        underlying: Underlying,
        collector: *Collector,
        appendFn: *const fn (ctx: *Collector, Underlying.ResultType) anyerror!void,

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            while (try self.underlying.parse(cursor)) |t| {
                try self.appendFn(self.collector, t);
            }
            return self.collector;
        }

        pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<collect {any} to {any}>", .{ @typeName(Collector), self.underlying });
        }
    };
}

pub inline fn arrayList(
    parser: anytype,
    list: *std.ArrayList(@TypeOf(parser).ResultType),
) CollectorParser(@TypeOf(parser), std.ArrayList(@TypeOf(parser).ResultType)) {
    return collect(std.ArrayList(@TypeOf(parser).ResultType), parser, list, std.ArrayList(@TypeOf(parser).ResultType).append);
}

test "Collect parsed chars to list" {
    var list = std.ArrayList(u8).init(std.testing.allocator);
    defer list.deinit();

    const p = arrayList(anyChar(), &list);

    try std.testing.expectEqualSlices(u8, &[_]u8{}, (try parseStr(std.testing.allocator, p, "")).?.items);
    try std.testing.expectEqualSlices(
        u8,
        &[_]u8{ 'a', 'b', 'c' },
        (try parseStr(std.testing.allocator, p, "abc")).?.items,
    );
}

pub inline fn tuple(parsers: anytype) TupleParser(@TypeOf(parsers)) {
    return .{ .parsers = parsers };
}

fn TupleParser(comptime Parsers: type) type {
    const struct_info: std.builtin.Type.Struct = switch (@typeInfo(Parsers)) {
        .Struct => |s| s,
        else => @compileError(std.fmt.comptimePrint(
            "Parsers should be struct with parsers but it is {any}.",
            .{@typeInfo(Parsers)},
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

        parsers: Parsers,

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            const orig_idx = cursor.idx;
            var result: ResultType = undefined;
            inline for (0..size) |i| {
                if (try self.parsers[i].parse(cursor)) |v| {
                    result[i] = v;
                } else {
                    log.debug(
                        "Parser {d} {any} was failed at {any}",
                        .{ i, self.parsers[i], cursor },
                    );
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

test "Parse the tuple of chars" {
    const p = tuple(.{ char('a'), char('b'), char('c') });
    try std.testing.expectEqual(.{ 'a', 'b', 'c' }, (try parseStr(std.testing.allocator, p, "abcdef")).?);
}

pub fn Either(comptime A: type, B: type) type {
    return union(enum) { left: A, right: B };
}

pub inline fn either(left: anytype, right: anytype) EitherParser(@TypeOf(left), @TypeOf(right)) {
    return .{ .left = left, .right = right };
}

fn EitherParser(comptime UnderlyingA: type, UnderlyingB: type) type {
    return struct {
        pub const ResultType = Either(UnderlyingA.ResultType, UnderlyingB.ResultType);

        const Self = @This();

        left: UnderlyingA,
        right: UnderlyingB,

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            const orig_idx = cursor.idx;
            if (try self.left.parse(cursor)) |a| {
                return .{ .left = a };
            }
            cursor.idx = orig_idx;
            if (try self.right.parse(cursor)) |b| {
                return .{ .right = b };
            }
            log.debug(
                "Parser both parsers {any} and {any} were failed at {any}",
                .{ self.left, self.right, cursor },
            );
            cursor.idx = orig_idx;
            return null;
        }

        pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<Either {any} or {any}>", .{ self.left, self.right });
        }
    };
}

test "Parse either of chars" {
    const p = either(char('a'), char('b'));

    try std.testing.expectEqual(null, try parseStr(std.testing.allocator, p, ""));
    try std.testing.expectEqual(null, try parseStr(std.testing.allocator, p, "c"));
    try std.testing.expectEqual(Either(u8, u8){ .left = 'a' }, try parseStr(std.testing.allocator, p, "a"));
    try std.testing.expectEqual(Either(u8, u8){ .right = 'b' }, try parseStr(std.testing.allocator, p, "b"));
}

test "Parse either of arrays" {
    const p = either(array(char('a'), 2), tuple(.{ char('a'), char('b') }));

    try std.testing.expectEqual(
        [_]u8{'a'} ** 2,
        (try parseStr(std.testing.allocator, p, "aa")).?.left,
    );
    try std.testing.expectEqual(
        .{ 'a', 'b' },
        (try parseStr(std.testing.allocator, p, "ab")).?.right,
    );
}

pub fn opt(parser: anytype) EitherParser(@TypeOf(parser), Successfull(void)) {
    return either(parser, successfull({}));
}

test "Parse optional value" {
    try std.testing.expectEqual(Either(u8, void){ .right = {} }, parseStr(std.testing.allocator, opt(char('a')), "b"));
    try std.testing.expectEqual(Either(u8, void){ .left = 'a' }, parseStr(std.testing.allocator, opt(char('a')), "a"));
}

pub inline fn oneCharOf(comptime chars: []const u8) OneCharOfParser(chars) {
    return .{};
}

fn OneCharOfParser(comptime chars: []const u8) type {
    return struct {
        pub const ResultType = u8;

        const Self = @This();

        const parser = anyChar();
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
                    const symbol = switch (ch) {
                        '\n' => "\\n",
                        '\t' => "\\t",
                        else => &[_]u8{ch},
                    };
                    log.debug("The '{s}' symbol was not found in {s}", .{ symbol, chars });
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

test "Parse one of chars" {
    const p = oneCharOf("ab");

    try std.testing.expectEqual(null, try parseStr(std.testing.allocator, p, ""));
    try std.testing.expectEqual(null, try parseStr(std.testing.allocator, p, "c"));
    try std.testing.expectEqual('a', try parseStr(std.testing.allocator, p, "a"));
    try std.testing.expectEqual('b', try parseStr(std.testing.allocator, p, "b"));
}

pub inline fn transform(
    comptime Result: type,
    parser: anytype,
    f: *const fn (a: @TypeOf(parser).ResultType) anyerror!Result,
) TransformParser(@TypeOf(parser), Result) {
    return .{ .underlying = parser, .mapFn = f };
}

fn TransformParser(comptime UnderlyingA: type, B: type) type {
    return struct {
        pub const ResultType = B;

        const Self = @This();

        underlying: UnderlyingA,
        mapFn: *const fn (a: UnderlyingA.ResultType) anyerror!B,

        fn parse(self: Self, cursor: *Cursor) anyerror!?ResultType {
            const orig_idx = cursor.idx;
            if (try self.underlying.parse(cursor)) |a| {
                return try self.mapFn(a);
            }
            cursor.idx = orig_idx;
            return null;
        }

        pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("<Transform result of the {any} to {any}>", .{ self.underlying, @typeName(B) });
        }
    };
}

test "Transform the parsed result" {
    const ParseInt = struct {
        fn parseInt(arr: [2]u8) anyerror!u8 {
            return try std.fmt.parseInt(u8, &arr, 10);
        }
    };

    const p = transform(u8, array(anyChar(), 2), ParseInt.parseInt);

    try std.testing.expectEqual(42, try parseStr(std.testing.allocator, p, "42"));
}

pub inline fn int(comptime T: type) IntParser(T, 128) {
    return .{};
}

fn IntParser(comptime T: type, max_buf_size: usize) type {
    return struct {
        pub const ResultType = T;

        const Self = @This();

        fn parse(_: Self, cursor: *Cursor) anyerror!?ResultType {
            const orig_idx = cursor.idx;
            var buf: [max_buf_size]u8 = undefined;
            const sign = oneCharOf("+-");
            var start: usize = 0;
            if (try sign.parse(cursor)) |s| {
                buf[0] = s;
                start += 1;
            }
            const number = slice(oneCharOf("0123456789_boXABCDF"), buf[start..]);
            if (try number.parse(cursor)) |n| {
                if (n.len > 0) {
                    const base: u8 = if (n[0] == '0' and n.len > 1)
                        switch (n[1]) {
                            'b', 'o', 'X' => 0,
                            else => 10,
                        }
                    else
                        10;
                    return std.fmt.parseInt(T, buf[0 .. n.len + start], base) catch |e| {
                        log.debug("The string \"{s}\" is not a number with base {d}", .{ n, base });
                        return e;
                    };
                }
            }
            log.debug("Parsing integer was failed at {any}", .{cursor});
            cursor.idx = orig_idx;
            return null;
        }

        pub fn format(_: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.writeAll("<Integer>");
        }
    };
}

test "Parse integers" {
    const p = int(i8);
    try std.testing.expectEqual(2, try parseStr(std.testing.allocator, p, "2"));
    try std.testing.expectEqual(2, try parseStr(std.testing.allocator, p, "+2"));
    try std.testing.expectEqual(-2, try parseStr(std.testing.allocator, p, "-2"));
    try std.testing.expectEqual(null, try parseStr(std.testing.allocator, p, "+-2"));
    try std.testing.expectEqual(2, try parseStr(std.testing.allocator, p, "0002"));
    try std.testing.expectEqual(2, try parseStr(std.testing.allocator, p, "0_0_0_2"));
    try std.testing.expectEqual(2, try parseStr(std.testing.allocator, p, "0b10"));
    try std.testing.expectEqual(2, try parseStr(std.testing.allocator, p, "+0b10"));
    try std.testing.expectEqual(-2, try parseStr(std.testing.allocator, p, "-0b10"));
    try std.testing.expectEqual(8, try parseStr(std.testing.allocator, p, "0o10"));
    try std.testing.expectEqual(10, try parseStr(std.testing.allocator, p, "0XA"));
}
