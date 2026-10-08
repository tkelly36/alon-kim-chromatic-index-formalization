# Chromatic-index bounds for uniform hypergraphs

This repository contains a Trellis/Lean formalization of the four headline
results in the manuscript *Improved bounds for the chromatic index of
\(k\)-uniform hypergraphs* by Sarah Frederickson, Yanli Hao, and Tom Kelly.

The development formalizes:

- the general edge-colouring theorem for uniform hypergraphs;
- the chromatic-index bound for 3-uniform, 2-simple hypergraphs;
- the chromatic-index bound for 3-uniform, 3-simple hypergraphs; and
- the chromatic-index bound for \(k\)-uniform, \(k\)-simple hypergraphs.

The corresponding principal Lean declarations are
`GeneralColoringTheorem`, `ThreeUniformTwoSimpleChromaticIndexBound`,
`ThreeUniformThreeSimpleChromaticIndexBound`, and
`KUniformKSimpleChromaticIndexBound`.

The formalization was produced using
[Trellis](https://github.com/wpegden/trellis), Wesley Pegden's
autoformalization harness for building verified Lean proof tablets.

## Status

This final snapshot contains 352 closed tablet nodes. The four target results
are kernel-checked, with no verifier blockers or unverified local closures at
the accepted checkpoint. A post-completion cleanup consolidated repeated
measure-zero, incidence-counting, and saturation arguments into reusable
lemmas without changing the four target statements.

The exact source checkpoint is
`4bea364b53d1d12b263d0e8ccfb34c6f1b71887c` (Trellis cycle 968), produced
with Trellis revision `d842acb02530079811bf48584318e1709596495e`.
The published snapshot passes the complete `lake build Tablet` check (3,882
jobs).

The project used no project-approved extra axioms:

```json
{
  "global": [],
  "nodes": {}
}
```

As with any formalization, identifying the Lean statements and definitions
with the intended mathematics still requires a human correspondence audit.

## Formalization viewer

The public [formalization viewer](https://tkelly36.github.io/alon-kim-chromatic-index-formalization/#GeneralColoringTheorem)
is the side-by-side TeX/Lean interface for reading and auditing the completed
development. It includes all four paper targets, their Lean semantic closures,
the full dependency outline, searchable proof nodes, Mathlib links, source
links, and reproducible build metadata.

The viewer is generated into `docs/` and deployed with GitHub Pages.

## Repository layout

- `formalization/` is the complete buildable Lean artifact.
- `formalization/Tablet/` contains paired `.lean` and `.tex` proof nodes.
- `formalization/Tablet/INDEX.md` records the node dependency graph.
- `formalization/Tablet.lean` is the generated root import surface.
- `docs/` is the generated public formalization viewer.
- `paper/README.md` records the frozen manuscript provenance and target labels.

The frozen manuscript source, Trellis runtime state, and supervisor history
are intentionally not distributed in this public repository.

## Reproducing the Lean check

The Lean toolchain and Mathlib revision are pinned. From the repository root:

```bash
cd formalization
lake build Tablet
```

## Reading the proof

Each theorem or definition node has a Lean file and a matching natural-language
TeX file. Start with the four principal declarations above, then use
`formalization/Tablet/INDEX.md` to follow their dependencies.

## Credits

The mathematical results are due to Sarah Frederickson, Yanli Hao, and Tom
Kelly. The formal artifact was generated with Trellis and checked with Lean
and Mathlib.
