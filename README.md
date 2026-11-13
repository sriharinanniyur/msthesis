# MS Thesis

Formal verification of integer multiplication algorithms in Lean 4.

## Notes
The formalizations are of abstract mathematical specifications of each algorithm, not of particular implementations. See the thesis itself for our philosophy and approach to specifying these algorithms. As a rule, we prioritize generality.

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain (`lean-toolchain`) and the Mathlib revision (`lake-manifest.json`) are pinned.

```
lake exe cache get
lake build
```

## Acknowledgments

Formalizations and proofs were developed with assistance from Fable 5.1 (Anthropic), GPT-6 Astra (OpenAI), and Aristotle (Harmonic). These tools were used to write specifications and proofs, search for Mathlib lemmas, and suggest formalization strategies.
