# FMCG40-Lean

A Lean 4 formalisation of the FMCG 4.0 framework's Signal-to-Shelf (StS) metric and Coupling Benefit Ratio (CBR), as defined in Alves and Treleaven (2026), "FMCG 4.0 and Signal-to-Shelf Analytics." This repository provides machine-checked proofs of the abstract mathematical properties of the framework — monotonicity of Signal-to-Shelf in elapsed time, well-definedness of the metrics, uniqueness of the exponential decay model, and conditions under which integrated decision-making yields a Coupling Benefit Ratio at or above 1 — as part of a UCL Computer Science PhD thesis.

## Status

**14 theorems, zero `sorry`, builds cleanly.** The complete formalisation lives in [`FMCG40/Basic.lean`](FMCG40/Basic.lean) — this is the actual, compilable source of truth for every result claimed by this project.

Numerical verification against the paper's Appendix 2 (ChillZen case study) is currently not included.

## Documentation

[`docs/theorem_reference.pdf`](docs/theorem_reference.pdf) (source: [`docs/theorem_reference.tex`](docs/theorem_reference.tex)) is a human-readable companion document covering all 14 theorems — plain-English statements, the underlying mathematics, and a short note on each theorem's significance to the paper's argument.

**Important:** the Lean code shown inside that PDF has been rewritten in a simplified ASCII notation (e.g. `R` for `ℝ`, `->` for `→`, `forall`/`exists` spelled out) purely so it typesets correctly under standard `pdflatex`. **It is not valid Lean and will not compile.** The real, working, compilable proofs are — and will only ever be — in [`FMCG40/Basic.lean`](FMCG40/Basic.lean). Treat the PDF as a reading aid, not a source file.

## Building

```bash
lake update
lake build
```
