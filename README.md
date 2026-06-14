# alist

`alist` is a Rust crate that implements association lists, inspired by Lisp, as a lightweight alternative to `HashMap` and `BTreeMap`.
The list is backed by a `Vec` of key-value pairs and keeps insertion order across insertions and removals.
It offers bookmarks for efficient repeated lookup and is particularly well-suited for small datasets.
Key-based operations scan linearly, so `AList` should be used only for small inputs and only with keys that meet
`FastEq`'s intended contract: compact key types with cheap equality.

---

## Features

- **Order Preservation**: Keys and values are stored in insertion order across insertions and removals.
- **Bookmark API**: Reuse a stored position for O(1) lookup when the bookmarked item has not moved; otherwise lookup falls back to a scan and refreshes the bookmark.
- **FastEq Keys**: Lookup and insertion APIs require `FastEq`, an `Eq` marker trait for types with trivial equality comparisons.
- **Convenience**: Includes iterators for keys, values, and entries, as well as standard collection utilities like `retain`, `clear`, and `shrink`.

---

## When to Use `alist`

- Small datasets only; key-based lookups, replacement insertions, removals, and entry access are `O(n)`.
- Applications that rely on predictable insertion order.
- Compact keys that implement `FastEq`, have cheap equality, and do not need to implement `Hash` or `Ord`.

---

## Choosing Key and Value Types

`AList` stores `(K, V)` pairs contiguously and performs linear scans for key lookup.
This makes the choice of `K` and `V` part of the performance model:

- Prefer compact keys and values. Large keys or values increase the stride between entries and can reduce cache-line efficiency during scans.
- Prefer keys with trivial equality. Lookup compares keys repeatedly, so an expensive `Eq` implementation can dominate runtime.
- `String` does not implement `FastEq` because string equality is `O(n)` in the string length. Prefer small identifiers, interned symbols, indices, or other compact keys when using `AList`.
- If values are large, consider storing an indirection such as `Box`, `Rc`, or `Arc` so scans move across compact pairs.

---

## Installation

Add `alist` to your `Cargo.toml`:

```bash
cargo add alist
```

or edit your Cargo.toml manually by adding:

```toml
[dependencies]
alist = "0.2"
```

## Examples

### Creating an `AList` and Adding Items

```rust
use alist::AList;

let mut alist = AList::new();
alist.insert('a', 42);
alist.insert('b', 99);

assert_eq!(alist.get(&'a'), Some(&42));
assert_eq!(alist.len(), 2);
```

Using the bookmark API:

```rust
use alist::AList;

let mut alist = AList::new();
alist.insert('a', 42);
alist.insert('b', 99);

let mut bookmark = alist.bookmark(&'a').unwrap();

assert_eq!(alist.get(&mut bookmark), Some(&42));
```

## Safety and Coverage

This crate contains no unsafe code.  

## Contributions

Contributions are always welcome! If you have ideas for new operations or improvements, feel free to open an issue or submit a pull request.

## License

This crate is licensed under the MIT License. See [LICENSE](LICENSE) for more details.
