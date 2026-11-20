# MS Thesis

Formalization of integer multiplication algorithms in Lean 4.

## Contents
See the thesis itself for our philosophy and approach to specifying these algorithms. We tend to prioritize formalizing abstract mathematical specifications of each algorithm.
- Packed long multiplication (`ks_improved`): on digit arrays with base generalized.
- Karatsuba: abstract and concrete specifications.
- Toom-Cook: general case, pure mathematical version.
- Toom-3: concrete interpolation sequence.
- Sch\"{o}nhage-Strassen I and II (SSC and SSF): pure mathematical specifications.

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain (`lean-toolchain`) and the Mathlib revision (`lake-manifest.json`) are pinned.

```
lake exe cache get
lake build
```

## Acknowledgments

Formalizations and proofs were developed with assistance from Fable 5.1 (Anthropic), GPT-6 Astra (OpenAI), and Aristotle (Harmonic). These tools were used to write specifications and proofs, search for Mathlib lemmas, and suggest formalization strategies.
