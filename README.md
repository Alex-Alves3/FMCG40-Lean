# FMCG40-Lean

A Lean 4 formalisation of the FMCG 4.0 framework's Signal-to-Shelf (StS) metric and Coupling Benefit Ratio (CBR), as defined in Alves and Treleaven (2026), "FMCG 4.0 and Signal-to-Shelf Analytics." This repository provides machine-checked proofs of the abstract mathematical properties of the framework — monotonicity of Signal-to-Shelf in elapsed time, well-definedness of the metrics, uniqueness of the exponential decay model, conditions under which integrated decision-making yields a Coupling Benefit Ratio at or above 1, and the properties of the chain from consumer signal to commercial strategy (Appendix A of the thesis) — as part of a UCL Computer Science PhD thesis.

## Status

**23 numbered theorems, zero `sorry`, zero new axioms, builds cleanly.**

- Theorems 1 to 14 (metrics: Signal-to-Shelf, Market Response, temporal decay, Coupling Benefit Ratio) are in [`FMCG40/Basic.lean`](FMCG40/Basic.lean).
- Theorems 15 to 23 (the chain of Appendix A, Sections A.5 and A.6: decomposition of ln CBR, exact condition for coupling benefit, boundedness of the rewards, budget monotonicity, safety, status propagation, well-typedness, sensitivity of CBR to λ with different times, sign of the speed term) are in [`FMCG40/Chain.lean`](FMCG40/Chain.lean). Some numbered theorems have several parts and helper lemmas, so `Chain.lean` contains more `theorem` declarations than numbered theorems.

Encoders, cosine similarity, the neural policy, the gradient boosting models and the ASP verifier enter as abstract functions with explicit hypotheses. The theorems hold for any implementation that satisfies those hypotheses.

These two files are the compilable source of truth for every result claimed by this project.

Numerical verification against the paper's Appendix 2 (ChillZen case study) is currently not included.

## Documentation

[`docs/theorem_reference.pdf`](docs/theorem_reference.pdf) (source: [`docs/theorem_reference.tex`](docs/theorem_reference.tex)) is a human-readable companion document covering all 23 numbered theorems — plain-English statements, the underlying mathematics, and a short note on each theorem's significance to the paper's argument.

**Important:** the Lean code shown inside that PDF has been rewritten in a simplified ASCII notation (e.g. `R` for `ℝ`, `->` for `→`, `forall`/`exists` spelled out) purely so it typesets correctly under standard `pdflatex`. **It is not valid Lean and will not compile.** The real, working, compilable proofs are — and will only ever be — in [`FMCG40/Basic.lean`](FMCG40/Basic.lean) and [`FMCG40/Chain.lean`](FMCG40/Chain.lean). Treat the PDF as a reading aid, not a source file.

## Building

```bash
lake update
lake exe cache get   # optional: downloads the prebuilt Mathlib
lake build
```

`FMCG40.lean` is the root module and imports every module, so `lake build` checks the whole development.
