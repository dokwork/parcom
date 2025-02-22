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

    const example = b.addExecutable(.{
        .name = "expression",
        .root_source_file = b.path("example/expression.zig"),
        .target = target,
        .optimize = optimize,
    });

    example.root_module.addImport("parcom", parcom);

    b.installArtifact(example);

    const run_example = b.addRunArtifact(example);
    if (b.args) |args| {
        run_example.addArgs(args);
    }

    const run_step = b.step("example", "Run example of parsing an expression");
    run_step.dependOn(&run_example.step);

    // ----- Unit tests -----
    const test_filters = b.option([]const []const u8, "test-filter", "Skip tests that do not match any filter") orelse &[0][]const u8{};

    const parcom_tests = b.addTest(.{
        .root_source_file = b.path("src/parcom.zig"),
        .target = target,
        .optimize = optimize,
        .filters = test_filters,
    });

    const run_parcom_tests = b.addRunArtifact(parcom_tests);

    const additional_tests = b.addTest(.{
        .root_source_file = b.path("test/test_pkg.zig"),
        .target = target,
        .optimize = optimize,
        .filters = test_filters,
    });

    additional_tests.root_module.addImport("parcom", parcom);

    const run_additional_tests = b.addRunArtifact(additional_tests);

    const example_tests = b.addTest(.{
        .root_source_file = b.path("example/expression.zig"),
        .target = target,
        .optimize = optimize,
        .filters = test_filters,
    });

    example_tests.root_module.addImport("parcom", parcom);

    const run_example_tests = b.addRunArtifact(example_tests);

    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_parcom_tests.step);
    test_step.dependOn(&run_additional_tests.step);
    test_step.dependOn(&run_example_tests.step);
}
