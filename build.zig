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

    // ----- Unit tests -----

    // -Dtest-filter=<a part of the test name>
    const test_filters = b.option(
        []const []const u8,
        "test-filter",
        "Skip tests that do not match any filter",
    ) orelse &[0][]const u8{};

    const parcom_tests = b.addTest(.{
        .root_source_file = b.path("src/parcom.zig"),
        .target = target,
        .optimize = optimize,
        .filters = test_filters,
    });

    const run_parcom_tests = b.addRunArtifact(parcom_tests);

    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_parcom_tests.step);

    // ----- Examples -----

    inline for ([_][]const u8{ "expression", "json" }) |example| {
        const example_source = std.fmt.comptimePrint("examples/{s}.zig", .{example});
        const exe = b.addExecutable(.{
            .name = example,
            .root_source_file = b.path(example_source),
            .target = target,
            .optimize = optimize,
        });

        exe.root_module.addImport("parcom", parcom);

        b.installArtifact(exe);

        const run_exe = b.addRunArtifact(exe);
        if (b.args) |args| {
            run_exe.addArgs(args);
        }
        const run_step = b.step(example, std.fmt.comptimePrint("Run example of {s}", .{example}));
        run_step.dependOn(&run_exe.step);

        const example_tests = b.addTest(.{
            .root_source_file = b.path(example_source),
            .target = target,
            .optimize = optimize,
            .filters = test_filters,
        });
        example_tests.root_module.addImport("parcom", parcom);

        const run_examples_tests = b.addRunArtifact(example_tests);
        test_step.dependOn(&run_examples_tests.step);
    }
}
