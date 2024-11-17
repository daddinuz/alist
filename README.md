# alist

`alist` is a Rust crate that implements association lists, inspired by Lisp, as lightweight alternative to `HashMap` and `BTreeMap`.
The list is backed by a `Vec` of key-value pairs and preserves the order of insertion.
It offers unique features like bookmarks for efficient item retrieval and is particularly well-suited for small datasets
or cases where insertion order matters.

---

## Features

- **Order Preservation**: Keys and values are stored in insertion order, making `alist` predictable and easy to iterate over.
- **Bookmark API**: Efficiently retrieve frequently accessed items with O(1) access when bookmarks are used and items remain unmoved.
- **Flexible Key Requirements**: Unlike `HashMap` or `BTreeMap`, `alist` requires keys to only implement `Eq`.
- **Convenience**: Includes iterators for keys, values, and entries, as well as standard collection utilities like `retain`, `clear`, and `shrink`.

---

## When to Use `alist`

- Small datasets where insertions and removals are infrequent.
- Applications that rely on predictable insertion order.
- When working with keys that are not `Hash` or `Ord`.

---

## Installation

Add `alist` to your `Cargo.toml`:

```bash
cargo add alist
```

or edit your Cargo.toml manually by adding:

```toml
[dependencies]
alist = "0.1"
```

## Examples

### Creating an `AList` and Adding Items

```rust
use alist::AList;

let mut alist = AList::new();
alist.insert("key1", 42);
alist.insert("key2", 99);

assert_eq!(alist.get("key1"), Some(&42));
assert_eq!(alist.len(), 2);
```

Using the Bookmark API:

```rust
use alist::{AList, Bookmark};

let mut alist = AList::new();
alist.insert("key1", 42);
alist.insert("key2", 99);

// Bookmarks' lifetime is independant of that of alists
let mut bookmark = alist.bookmark("key1").unwrap();

// Fast retrieval using bookmark
assert_eq!(alist.get(&mut bookmark), Some(&42));
```

## Safety and Coverage

This crate contains no unsafe code.  
All tests run under [miri](https://github.com/rust-lang/miri) and the tests cover about 50% of the code.  
You can generate the coverage report using [tarpaulin](https://github.com/xd009642/tarpaulin).

## Contributions

Contributions are always welcome! If you have ideas for new operations or improvements, feel free to open an issue or submit a pull request.

## License

This crate is licensed under the MIT License. See [LICENSE](LICENSE) for more details.
