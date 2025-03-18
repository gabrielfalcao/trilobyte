# TriloByte

`TriloByte` is a data-structure representing `3` bits, primarily
designed for representing masks and the `3` role permissions of
unix files (user, group and other).

For example, a unix file with mode `007` can be represented with
`3` trilobytes:

```
use trilobyte::TriloByte;

let trilobytes = [
    TriloByte(false, false, false),
    TriloByte(false, false, false),
    TriloByte(true, true, true),
];
let mode = trilobytes.iter().map(|t| t.to_string_octal()).collect::<String>();
assert_eq!(mode, "007");
```


[![Continuous Integration](https://github.com/gabrielfalcao/trilobyte/actions/workflows/ci.yml/badge.svg)](https://github.com/gabrielfalcao/trilobyte/actions/workflows/ci.yml)
