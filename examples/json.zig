const std = @import("std");
const p = @import("parcom");

const KV = struct { []const u8, Json };

const Json = union(enum) {
    Null,
    boolean: bool,
    number: f64,
    string: []const u8,
    array: []Json,
    object: []KV,
};

fn jsonParser(alloc: std.mem.Allocator) !p.TaggedParser(Json) {
    const json = p.deferred(Json, alloc, jsonParser);

    const Null: Json = .Null;
    const jnull = p.word("null").as(Null);

    const jtrue = p.word("true").as(Json{ .boolean = true });
    const jfalse = p.word("false").as(Json{ .boolean = false });
    const jboolean = jtrue.orElse(jfalse).transform(Json, {}, getFromEither);

    const jnumber = p.float(f64, 10).transform(Json, {}, struct {
        fn asJson(_: void, value: f64) !Json {
            return .{ .number = value };
        }
    }.asJson);

    const jstring_content = p.anyChar().suchThat({}, struct {
        fn filter(_: void, value: u8) bool {
            return value != '"';
        }
    }.filter).repeat(alloc, .{}).transform(Json, {}, struct {
        fn asJson(_: void, value: []u8) !Json {
            return .{ .string = value };
        }
    }.asJson);
    const jstring = p.char('"').rightThen(jstring_content).leftThen(p.char('"')).coerce(Json);

    // json(,json)*
    const jarray_content = json.andThen(p.char(',').rightThen(json).repeat(alloc, .{})).transform(
        Json,
        alloc,
        struct {
            fn asJson(allocator: std.mem.Allocator, value: struct { Json, []Json }) !Json {
                var buffer = try allocator.alloc(Json, value[1].len + 1);
                buffer[0] = value[0];
                @memcpy(buffer[1..], value[1]);
                return .{ .array = buffer };
            }
        }.asJson,
    );
    const jarray = p.char('[').rightThen(jarray_content).leftThen(p.char(']')).coerce(Json);

    const kv = jstring.leftThen(p.char(':')).andThen(json).transform(KV, {}, struct {
        fn asKV(_: void, value: struct { Json, Json }) !KV {
            return .{ value[0].string, value[1] };
        }
    }.asKV);
    const jobject_content = kv.andThen(p.char(',').rightThen(kv).repeat(alloc, .{})).transform(
        Json,
        alloc,
        struct {
            fn asJson(allocator: std.mem.Allocator, value: struct { KV, []KV }) !Json {
                var buffer = try allocator.alloc(KV, value[1].len + 1);
                buffer[0] = value[0];
                @memcpy(buffer[1..], value[1]);
                return .{ .object = buffer };
            }
        }.asJson,
    );
    const jobject = p.char('{').rightThen(jobject_content).leftThen(p.char('}')).coerce(Json);

    return jnull
        .orElse(jboolean).transform(Json, {}, getFromEither)
        .orElse(jnumber).transform(Json, {}, getFromEither)
        .orElse(jstring).transform(Json, {}, getFromEither)
        .orElse(jarray).transform(Json, {}, getFromEither)
        .orElse(jobject).transform(Json, {}, getFromEither)
        .taggedAllocated(alloc);
}

pub fn getFromEither(_: void, value: p.Either(Json, Json)) anyerror!Json {
    return switch (value) {
        .left => |v| v,
        .right => |v| v,
    };
}

test "simple example" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const json =
        \\[
        \\  "Simple JSON example",
        \\  {"object with 1 member":["array with 1 element"]},
        \\  {},
        \\  [],
        \\  -42,
        \\  true,
        \\  false,
        \\  null,
        \\  {
        \\      "integer": 1234567890,
        \\      "real": -9876.543210,
        \\      "e": 0.123456789e-12,
        \\      "E": 1.234567890E+34,
        \\      "":  23456789012E66,
        \\      "zero": 0,
        \\      "one": 1,
        \\      "space": " "
        \\   }
        \\]
    ;

    const parser = try jsonParser(arena.allocator());

    try std.testing.expect(try parser.parseString(json) != null);
}
