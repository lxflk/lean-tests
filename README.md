# LeanTests

A small Lean project for trying proof snippets.

Put reusable theorem files under `LeanTests/` and import them from
`LeanTests.lean` so `lake build` checks them.

```sh
lake build
lake env lean LeanTests/Basic.lean
```
