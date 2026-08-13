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

If a change affects a numbered paper result or one of the public Blueprint
declarations, also update the corresponding node under `blueprint/`, its entry
in `blueprint/links.json`, and `SEMANTIC_REVIEW.md`. A prior semantic sign-off is
commit-specific: reset the affected row to pending until the revised mapping is
reviewed. Then run:

```sh
./blueprint/scripts/build-site.sh
```

Keep `main.tex` authoritative. The Blueprint should describe correspondence
and known qualifications concisely, rather than silently changing the paper's
mathematical statement.
