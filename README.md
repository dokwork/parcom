# parcom

[![parcom ci](https://github.com/dokwork/parcom/actions/workflows/ci.yml/badge.svg)](https://github.com/dokwork/parcom/actions/workflows/ci.yml)
![zig version](https://img.shields.io/badge/zig%20version-0.14.0-fcca77)

_Consume input, not memory_

> [!WARNING]  
> This library is underdeveloped. API is not stable.

This library provides an implementation of the parser combinators.

Three different types of parser implementations exist:

 - The base parser implementations contain the logic for parsing input and serve
   as the fundamental building blocks;
 - The `ParserCombinator`provides methods to combine parsers and create new ones;
 - The `TaggedParser` erases the type of the underlying parser and simplifies
   the parser's type declaration.

`Parcom` offers two options for consuming data:
 - parse the entire input string at once,
 - or consume and parse byte by byte from `AnyReader`.

When the input is a reader, `parcom` works as a buffered reader. It reads few
bytes to the buffer and then parse them.

The result of parsing by any parser can be an appropriate value in successful
case, or `null` if parsing was failed. In successful case not all input can be
consumed. If you have to be sure, that every byte was consumed and parsed, use
`end()` parser explicitly.

## Installation

Fetch `parcom` from github:
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
Add `parcom` module to your `build.zig`:
```zig
    const parcom = b.dependency("parcom", .{
        .target = target,
        .optimize = optimize,
    });
    ...
    exe.root_module.addImport("parcom", parcom.module("parcom"));
```

## Quick start

Let's create a parser, which will parse and execute a simple math expression with follow
grammar:
```
# The `value` is an unsigned integer number or an expression in brackets
Value   := [0-9]+ / '(' Expr ')'
# The `product` is an operation of multiplication or division of two or more values
Product := Value (('*' / '/') Value)*
# The `sum` is an operation of adding or substraction of two or more values
Sum     := Product (('+' / '-') Product)*
# The `expression` is a sequence of all above
Expr    := Sum
```

### Base parsers

The value from the grammar above is a repeated symbols from the range ['0', '9'].
The base parser in `parcom` is `AnyChar`
```zig
```


## Documentation
[https://dokwork.github.io/parcom/index.html](https://dokwork.github.io/parcom/index.html)

## Examples

 - [The parser of a math expression](examples/expression.zig)
 - [The json parser](examples/json.zig)
