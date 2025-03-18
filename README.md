# TriloByte

`TriloByte` is a data-structure representing `3` bits, primarily
designed for representing masks and the `3` role permissions of
unix files (user, group and other).

For example, a unix file with mode `007` can be represented with
`3` trilobytes:

```rust
(
    TriloByte(false, false, false),
    TriloByte(false, false, false),
    TriloByte(true, true, true),
)
```

[![Continuous Integration](https://github.com/gabrielfalcao/trilobyte/actions/workflows/ci.yml/badge.svg)](https://github.com/gabrielfalcao/trilobyte/actions/workflows/ci.yml)
