//! This is a simple implementation of a JSON parser. While it isn't fully correct, it demonstrates
//! the flexibility of the `parcom` library and serves as a proof of concept for optimization through
//! the input truncation.
//!
//! This example can be run to parse json from the stdin:
//! ```sh
//! echo '{ "hello" : "world" }' | zig build json
//! ```
//! By default, the result of parsing is ignored.
//! To print the parsed json to stdout use `-o` argument. In that case the stdin will be parsed,
//! and AST for parsed input built. Then this AST will be serialized back to the string, and printed
//! to the stdout:
//! ```sh
//! echo '{ "hello" : "world" }' | zig build json -- -o
//! > { "hello": "world" }
//! ```
//!
//! The default mode makes it possible to parse a huge input with minimum
//! memory consumption. For example, to parse 300 mb input from
//! https://jsoneditoronline.org/indepth/datasets/json-file-example/#a-large-json-document
//! this parser needs only approximately 30 mb of memory:
//! ```sh
//! cat users_1m.json | /usr/bin/time -l zig build json                                                                  cut-combinator * 4:49 PM
//! > Json has been parsed.
//! >        98.21 real        95.75 user         2.16 sys
//! >             34160640  maximum resident set size
//! >                    0  average shared memory size
//! >                    0  average unshared data size
//! >                    0  average unshared stack size
//! >                12718  page reclaims
//! >                   12  page faults
//! >                    0  swaps
//! >                    0  block input operations
//! >                    0  block output operations
//! >                    0  messages sent
//! >                    0  messages received
//! >                    0  signals received
//! >                 2162  voluntary context switches
//! >                12647  involuntary context switches
//! >            190536778  instructions retired
//! >             93818029  cycles elapsed
//! >             16238592  peak memory footprint
//! ```
const std = @import("std");
const p = @import("parcom");

/// The simple implementation of json parser that provides a result with passed target type.
/// The `TargetType` should implement interface equal to `Json` and `Void` implementations in this
/// example.
fn JsonParser(comptime TargetType: type) type {
    return struct {
        fn taggedParser(alloc: std.mem.Allocator) !p.TaggedParser(TargetType) {
            const json = p.deferred(TargetType, alloc, taggedParser);

            const jnull = p.word("null").as(TargetType.fromNull());

            const jtrue = p.word("true").as(true);
            const jfalse = p.word("false").as(false);
            const jboolean = jtrue.orElse(jfalse).transform(TargetType, {}, struct {
                fn targetType(_: void, either: p.Either(bool, bool)) !TargetType {
                    const value = switch (either) {
                        .left => |v| v,
                        .right => |v| v,
                    };
                    return TargetType.fromBoolean(value);
                }
            }.targetType);

            const jnumber = p.float(f64, 64).transform(TargetType, {}, struct {
                fn targetType(_: void, value: f64) !TargetType {
                    return TargetType.fromNumber(value);
                }
            }.targetType);

            const jstring_content = p.anyChar().suchThat({}, struct {
                fn filter(_: void, value: u8) bool {
                    return value != '"';
                }
            }.filter).repeat(alloc, .{}).transform(TargetType, alloc, TargetType.fromString);
            const jstring = sep('"').rightThen(jstring_content).leftThen(sep('"'));

            // (json(,)?)*
            const jarray_content = json.leftThen(sep(',').optional()).repeat(alloc, .{})
                .transform(TargetType, alloc, TargetType.fromArray);
            const jarray = sep('[').rightThen(jarray_content).leftThen(sep(']'));

            const kv = jstring.leftThen(sep(':')).andThen(json)
                .transform(TargetType.KV, {}, TargetType.KV.fromTuple);

            const jobject_content = kv.leftThen(sep(',').optional()).repeat(alloc, .{})
                .transform(TargetType, alloc, TargetType.fromObject);
            const jobject = sep('{').rightThen(jobject_content).leftThen(sep('}'));

            return jnull
                .orElse(jboolean).transform(TargetType, {}, FromEither(TargetType).get)
                .orElse(jnumber).transform(TargetType, {}, FromEither(TargetType).get)
                .orElse(jstring).transform(TargetType, {}, FromEither(TargetType).get)
                .orElse(jarray).transform(TargetType, {}, FromEither(TargetType).get)
                .orElse(jobject).transform(TargetType, {}, FromEither(TargetType).get)
                .taggedAllocated(alloc);
        }
    };
}

const spaces = p.oneCharOf(" \t\n\r").skip(.{});
inline fn sep(comptime char: u8) @TypeOf(spaces.rightThen(p.char(char)).leftThen(spaces).cut()) {
    return spaces.rightThen(p.char(char)).leftThen(spaces)
        // This is the most important part of this example.
        // It crops the buffer of input every time, when a separator and spaces around it are parsed.
        // The main idea here is if you meet, for example, '{' and doesn't parse the whole object
        // successfully, you shouldn't try to use another parser, because the input is obviously broken.
        .cut();
}

fn FromEither(comptime T: type) type {
    return struct {
        fn get(_: void, value: p.Either(T, T)) anyerror!T {
            return switch (value) {
                .left => |v| v,
                .right => |v| v,
            };
        }
    };
}

/// The AST for json.
const Json = union(enum) {
    const KV = struct {
        key: []const u8,
        value: Json,

        fn fromTuple(_: void, value: struct { Json, Json }) !KV {
            return .{ .key = value[0].string, .value = value[1] };
        }

        pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
            try writer.print("\"{s}\": {any}", .{ self.key, self.value });
        }
    };

    Null,
    boolean: bool,
    number: f64,
    string: []const u8,
    array: []Json,
    object: []KV,

    fn fromNull() Json {
        return .Null;
    }

    fn fromBoolean(boolean: bool) Json {
        return .{ .boolean = boolean };
    }

    fn fromNumber(number: f64) Json {
        return .{ .number = number };
    }

    fn fromString(_: std.mem.Allocator, string: []const u8) !Json {
        return .{ .string = string };
    }

    fn fromArray(_: std.mem.Allocator, array: []Json) !Json {
        return .{ .array = array };
    }

    fn fromObject(_: std.mem.Allocator, object: []KV) !Json {
        return .{ .object = object };
    }

    pub fn format(self: @This(), comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
        switch (self) {
            .Null => try writer.writeAll("null"),
            .boolean => |b| try writer.print("{any}", .{b}),
            .number => |n| try writer.print("{any}", .{n}),
            .string => |s| try writer.print("\"{s}\"", .{s}),
            .array => |arr| {
                if (arr.len == 0) {
                    try writer.writeAll("[ ]");
                    return;
                }
                try writer.writeAll("[ ");
                for (0..arr.len - 1) |i| {
                    try writer.print("{any}, ", .{arr[i]});
                }
                try writer.print("{any} ]", .{arr[arr.len - 1]});
            },
            .object => |obj| try writer.print("{any}", .{obj}),
        }
    }
};

/// The implementation of the `TargetType`, which destructs all parsed results and frees all allocated memory
/// during the parsed process. It is used to show how cutting input can be used to minimize required
/// for parsing memory.
const Void = enum {
    const KV = struct {
        key: Void,
        value: Void,
        fn fromTuple(_: void, _: struct { Void, Void }) !KV {
            return .{ .key = .void, .value = .void };
        }
    };

    void,

    fn fromNull() Void {
        return .void;
    }

    fn fromBoolean(_: bool) Void {
        return .void;
    }

    fn fromNumber(_: f64) Void {
        return .void;
    }

    fn fromString(alloc: std.mem.Allocator, value: []const u8) !Void {
        alloc.free(value);
        return .void;
    }

    fn fromArray(alloc: std.mem.Allocator, value: []Void) !Void {
        alloc.free(value);
        return .void;
    }

    fn fromObject(alloc: std.mem.Allocator, value: []KV) !Void {
        alloc.free(value);
        return .void;
    }
};

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer if (gpa.deinit() == .leak) @panic("MEMORY LEAK DETECTED!");
    var arena = std.heap.ArenaAllocator.init(gpa.allocator());
    defer arena.deinit();

    const alloc = arena.allocator();

    const stdout = std.io.getStdOut().writer();
    const stderr = std.io.getStdErr().writer();

    const reader = std.io.getStdIn().reader();

    var args = try std.process.argsWithAllocator(alloc);
    // skip the path to the program
    _ = args.next();

    const should_output = if (args.next()) |arg| std.mem.eql(u8, arg, "-o") else false;

    if (should_output) {
        const parser = try JsonParser(Json).taggedParser(alloc);
        if (try parser.parseFromReader(alloc, reader.any())) |result| {
            try stdout.print("{any}", .{result});
        } else {
            try stderr.print("Json was not parsed", .{});
        }
    } else {
        const parser = try JsonParser(Void).taggedParser(alloc);
        if (try parser.parseFromReader(alloc, reader.any())) |_| {
            try stdout.print("Json has been parsed.\n", .{});
        } else {
            try stderr.print("Json was not parsed", .{});
        }
    }
}

test "null" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const parser = try JsonParser(Json).taggedParser(arena.allocator());
    try std.testing.expectEqual(.Null, try parser.parseString("null"));
}

test "boolean" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const parser = try JsonParser(Json).taggedParser(arena.allocator());
    try std.testing.expectEqual(Json{ .boolean = true }, try parser.parseString("true"));
    try std.testing.expectEqual(Json{ .boolean = false }, try parser.parseString("false"));
}

test "integer" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const parser = try JsonParser(Json).taggedParser(arena.allocator());
    try std.testing.expectEqual(Json{ .number = 42 }, try parser.parseString("42"));
}

test "float" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const parser = try JsonParser(Json).taggedParser(arena.allocator());
    try std.testing.expectEqual(Json{ .number = 4.2 }, try parser.parseString("42e-1"));
}

test "string" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const parser = try JsonParser(Json).taggedParser(arena.allocator());
    const result = (try parser.parseString("\"Hello world!\"")).?;
    try std.testing.expect(result == .string);
    try std.testing.expectEqualStrings("Hello world!", result.string);
}

test "empty array" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const parser = try JsonParser(Json).taggedParser(arena.allocator());
    const result = (try parser.parseString("[]")).?;
    try std.testing.expect(result == .array);
    try std.testing.expectEqualSlices(Json, &[_]Json{}, result.array);
}

test "array" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const parser = try JsonParser(Json).taggedParser(arena.allocator());
    const result = (try parser.parseString("[null, 1, true]")).?;
    try std.testing.expect(result == .array);
    try std.testing.expectEqualSlices(Json, &[_]Json{ .Null, .{ .number = 1 }, .{ .boolean = true } }, result.array);
}

test "empty object" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const parser = try JsonParser(Json).taggedParser(arena.allocator());
    const result = (try parser.parseString("{}")).?;
    try std.testing.expect(result == .object);
    try std.testing.expectEqualSlices(Json.KV, &[_]Json.KV{}, result.object);
}

test "object" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const parser = try JsonParser(Json).taggedParser(arena.allocator());
    const result = (try parser.parseString(
        \\{
        \\  "a" : true,
        \\  "b":0,"c":"yes"}
    )).?;
    try std.testing.expect(result == .object);
    try std.testing.expectEqualDeep(
        &[_]Json.KV{
            .{ .key = "a", .value = .{ .boolean = true } },
            .{ .key = "b", .value = .{ .number = 0 } },
            .{ .key = "c", .value = .{ .string = "yes" } },
        },
        result.object,
    );
}

// Test with few nodes of json from here:
// https://jsoneditoronline.org/indepth/datasets/json-file-example/#a-large-json-document
test "simple example" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const parser = try JsonParser(Json).taggedParser(arena.allocator());

    const json =
        \\[
        \\  {
        \\    "id": 0,
        \\    "name": "Elijah",
        \\    "city": "Austin",
        \\    "age": 78,
        \\    "friends": [
        \\      {
        \\        "name": "Michelle",
        \\        "hobbies": [
        \\          "Watching Sports",
        \\          "Reading",
        \\          "Skiing & Snowboarding"
        \\        ]
        \\      },
        \\      {
        \\        "name": "Robert",
        \\        "hobbies": [
        \\          "Traveling",
        \\          "Video Games"
        \\        ]
        \\      }
        \\    ]
        \\  },
        \\  {
        \\    "id": 1,
        \\    "name": "Noah",
        \\    "city": "Boston",
        \\    "age": 97,
        \\    "friends": [
        \\      {
        \\        "name": "Oliver",
        \\        "hobbies": [
        \\          "Watching Sports",
        \\          "Skiing & Snowboarding",
        \\          "Collecting"
        \\        ]
        \\      },
        \\      {
        \\        "name": "Olivia",
        \\        "hobbies": [
        \\          "Running",
        \\          "Music",
        \\          "Woodworking"
        \\        ]
        \\      },
        \\      {
        \\        "name": "Robert",
        \\        "hobbies": [
        \\          "Woodworking",
        \\          "Calligraphy",
        \\          "Genealogy"
        \\        ]
        \\      },
        \\      {
        \\        "name": "Ava",
        \\        "hobbies": [
        \\          "Walking",
        \\          "Church Activities"
        \\        ]
        \\      },
        \\      {
        \\        "name": "Michael",
        \\        "hobbies": [
        \\          "Music",
        \\          "Church Activities"
        \\        ]
        \\      },
        \\      {
        \\        "name": "Michael",
        \\        "hobbies": [
        \\          "Martial Arts",
        \\          "Painting",
        \\          "Jewelry Making"
        \\        ]
        \\      }
        \\    ]
        \\  },
        \\  {
        \\    "id": 2,
        \\    "name": "Evy",
        \\    "city": "San Diego",
        \\    "age": 48,
        \\    "friends": [
        \\      {
        \\        "name": "Joe",
        \\        "hobbies": [
        \\          "Reading",
        \\          "Volunteer Work"
        \\        ]
        \\      },
        \\      {
        \\        "name": "Joe",
        \\        "hobbies": [
        \\          "Genealogy",
        \\          "Golf"
        \\        ]
        \\      },
        \\      {
        \\        "name": "Oliver",
        \\        "hobbies": [
        \\          "Collecting",
        \\          "Writing",
        \\          "Bicycling"
        \\        ]
        \\      },
        \\      {
        \\        "name": "Liam",
        \\        "hobbies": [
        \\          "Church Activities",
        \\          "Jewelry Making"
        \\        ]
        \\      },
        \\      {
        \\        "name": "Amelia",
        \\        "hobbies": [
        \\          "Calligraphy",
        \\          "Dancing"
        \\        ]
        \\      }
        \\    ]
        \\  }
        \\]
    ;

    const result = (try parser.parseString(json)).?;
    try std.testing.expect(result == .array);
    try std.testing.expectEqual(3, result.array.len);
}
