const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // ----- Main module -----

    const parcom = b.addModule("parcom", .{
        .root_source_file = b.path("src/parcom.zig"),
        .target = target,
        .optimize = optimize,
    });

    // to test docs run:
    // python -m http.server 8000 -d zig-out/docs
    const docs = b.addObject(.{
        .name = "parcom",
        .root_source_file = b.path("src/parcom.zig"),
        .target = target,
        .optimize = .Debug,
    });
    const install_docs = b.addInstallDirectory(.{
        .install_dir = .prefix,
        .install_subdir = "docs",
        .source_dir = docs.getEmittedDocs(),
    });
    b.step("docs", "Build docs").dependOn(&install_docs.step);

    // ----- Example -----
    // to handle many examples see
    // https://github.com/zigzap/zap/blob/master/build.zig#L49

    const examples = b.addExecutable(.{
        .name = "examples",
        .root_source_file = b.path("examples/expression.zig"),
        .target = target,
        .optimize = optimize,
    });

    examples.root_module.addImport("parcom", parcom);

    b.installArtifact(examples);

    const run_examples = b.addRunArtifact(examples);
    if (b.args) |args| {
        run_examples.addArgs(args);
    }

    const run_step = b.step("expression", "Run example of parsing a math expression");
    run_step.dependOn(&run_examples.step);

    // ----- Unit tests -----
    const test_filters = b.option([]const []const u8, "test-filter", "Skip tests that do not match any filter") orelse &[0][]const u8{};

    const parcom_tests = b.addTest(.{
        .root_source_file = b.path("src/parcom.zig"),
        .target = target,
        .optimize = optimize,
        .filters = test_filters,
    });

    const run_parcom_tests = b.addRunArtifact(parcom_tests);

    const example_tests = b.addTest(.{
        .root_source_file = b.path("examples/expression.zig"),
        .target = target,
        .optimize = optimize,
        .filters = test_filters,
    });

    example_tests.root_module.addImport("parcom", parcom);

    const run_examples_tests = b.addRunArtifact(example_tests);

    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_parcom_tests.step);
    test_step.dependOn(&run_examples_tests.step);
}
