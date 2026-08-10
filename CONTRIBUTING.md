# Contributing

Keep declarations in paper order and add only complete proofs. Before opening a
pull request, run:

```sh
lake build
./scripts/audit.sh
```

Do not add `sorry`, `admit`, custom axioms, `opaque`, `unsafe`, or `partial`
proof placeholders, or computation-based equality workarounds. Prefer existing
mathlib abstractions and small reusable lemmas. If a paper statement needs a
correction or an implicit hypothesis, record the discrepancy in
`FORMALIZATION.md` before building on it.
