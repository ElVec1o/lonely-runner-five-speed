# The five-speed lonely runner spectrum below 1/5: a kernel-checked proof

Version 1.0.1 (19 November 2026). Author: Vico Bonfioli. License: CC-BY-4.0 (`LICENSE.md`).
Repository: https://github.com/ElVec1o/lonely-runner-five-speed
DOI: https://doi.org/10.5281/zenodo.24358071 (all versions, concept DOI); version 1.0.0: https://doi.org/10.5281/zenodo.24358072. The DOI of version 1.0.1 is added here after its release.
Version 1.0.1 adds the generated modules of eight representatives (265, 304, 927, 1075, 1336, 1343, 1524, 1763) that version 1.0.0 omitted.
Paper: `paper/main.pdf` (17 pages; source `paper/main.tex`). Not peer reviewed.

## What this is

For positive integer speeds `v_1,...,v_n` let `ML(v) = max_t min_i dist(t v_i, Z)`, where `dist` is the distance to the nearest integer (the "maximum loneliness" of the lonely runner problem).
This repository contains a complete formalization in Lean 4 with Mathlib of the following statement, together with a paper that explains the proof.

> For five distinct positive integer speeds with `ML(v) < 1/5` there is an integer `s >= 1` with `ML(v) = s/(5s+1)`. Every such value occurs, for `v = (1,2,3,4,5s)`. Hence the set of values of `ML` below `1/5` on five distinct positive integer speeds is exactly `{s/(5s+1) : s >= 1}`.

In Kravitz's terminology this is his spectrum conjecture for five runners, with all values attained. No hypothesis is left over, and the main theorems depend on exactly the three standard axioms `propext`, `Classical.choice`, `Quot.sound` (no `sorry`, no `native_decide`).

The proof is a computer-assisted case analysis: a tree of choices for the first rows of a reduced basis of the relation lattice, two critical two-dimensional subtori on which the value is computed by hand, and a finite certificate (1,965 representatives of second-level nodes, 81,436 leaf classes, 9,593,060 lines, as counted in the paper) produced by Rust programs and checked by the Lean kernel.
**The method is that of Yi, Gill and Bu for four speeds (arXiv:2610.40694), and the five-speed value family `(1,2,3,4,5s)` is due to Kravitz.** To our reading of version 1 of Yi, Gill and Bu, they reduce five speeds to norm below 33,750 and do not enumerate the remaining finite set; Cordella lists the near-tight quintuples up to speed 130.
We do not know of another complete proof of the five-speed statement, on paper or formal, as of our searches of 15 and 17 November 2026 (not repeated later); whether one exists must be checked against the literature, not against this repository.

## Main results

| paper | Lean declaration (namespace `LRSpectrumFull.L5S5`) | module | statement |
|---|---|---|---|
| Theorem 1 | `five_speed_spectrum_final` | `L5S5/FiveSpeedFinal3.lean` | `v : Fin 5 -> Int`, all `v i > 0`, `v` injective, `ML v < 1/5` implies there is `s >= 1` with `ML v = s/(5s+1)` |
| Theorem 2 | `five_speed_attained` | `L5S5/FiveSpeedOfTree.lean` | for every `s >= 1`, `(1,2,3,4,5s)` are five distinct positive integers with `ML = s/(5s+1)` |
| Corollary 3 | `five_speed_spectrum_iff_final` | `L5S5/FiveSpeedFinal4.lean` | for `x : Real`: (`x = ML v` for five distinct positive integer speeds and `x < 1/5`) iff (`x = s/(5s+1)` for some `s >= 1`) |

`ML v := sSup (Set.range (gap v))` with `gap v t := inf'_i nearestIntDist (v i * t)` and `nearestIntDist x := min (Int.fract x) (1 - Int.fract x)`
(`LRSpectrumFull/MaxLoneliness.lean`, `NearestInteger.lean`; 218 lines in all). Read these before trusting the English above; `repro/check_axioms.lean` prints the definitions.

## Verify in three commands

Needs `elan`, the Mathlib cache for the pinned revision (`lake exe cache get`; not done by the scripts), Rust (std only) and about 24 GB of memory. Run from the repository root.

```
cd repro
bash build.sh --plan                                               # validate sources, hashes, build order, pins; builds nothing
bash regen_data.sh --full --install --steps build,v3,s4o,lines    # restore the 8,102 regenerable generated modules omitted for size and compare sha256 (minutes)
bash build.sh --run && bash check_axioms.sh                        # build the 17,598 modules one at a time (about 36.8 h), then print and judge the axioms: expect VERDICT: PASS
```

The first command reports `PLAN INCOMPLETE` (exit 4) in the shipped state, because the regenerable generated modules are missing; after the second command it reports `PLAN VALID`.
A quick check that needs no Lean: `shasum -a 256 -c CHECKSUMS.sha256 | grep -vc ': OK'` prints `0`.
Never run a bare `lake build` in `lean/` (one lean process of this project needs 4 to 10 GB, and lake starts one per core); the lakefile has no default target for this reason.

## What is checked, and by whom

* **The Lean kernel** checks the proofs of the three theorems above, including every generated certificate. `repro/check_axioms.sh` prints `#print axioms` for them and for two planted-`sorry` controls and judges the output; the recorded output is in `repro/expected_output/`.
* **A source scan** (`repro/tools/source_scan.sh`) of all 17,598 modules of the import closure, with comments stripped, finds no `sorry`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `extern`, `opaque` or `ofReduceBool`. The planted-`sorry` control files of the development tree (48 files) are not in the closure and are not shipped.
* **The Rust generators are untrusted.** The kernel re-checks every generated data blob against Lean definitions whose soundness theorems are proved in Lean; a wrong generator can only make the build fail.
* **Not checked by anyone**: that the Lean statement is the mathematical statement the reader has in mind (read the definitions above), and the counts quoted in the paper about the certificate (they describe the generated data; no theorem depends on them). No human has reviewed the proofs.

Versions: Lean 4.30.0 (`leanprover/lean4:v4.30.0`), Mathlib at revision `c5ea00351c28e24afc9f0f84379aa41082b1188f` (pinned in `lean/lake-manifest.json`).

## Honest limits

1. **No clean from-scratch rebuild** (about 36.8 h of Lean time, a cost-model figure) was run. The proof was built incrementally over 17 to 19 November 2026; the build, plan and axiom scripts were exercised on that already built tree. `repro/README.md` lists what was observed and what was not.
2. **Not claimed:** any first proof of the five-speed statement; repeated, zero, negative or non-integer speeds; other numbers of speeds; shifted versions; values `>= 1/5`; the lonely runner conjecture. The paper has not been peer reviewed.
3. **Prior-art check.** The five-speed-specific search for other proofs or formalizations was last run on 17 November 2026, and only version 1 of Yi, Gill and Bu was read. The sentence "no other complete proof is known to us" is dated and may expire.
4. **Partial regeneration.** Part of the generated data is regenerated by script and compared byte for byte; several generator families are shipped as sources with manifest hashes only, and the T4 class tables are copied inputs (`repro/README.md`, sections 7 and 8). The eight representatives 265, 304, 927, 1075, 1336, 1343, 1524 and 1763 (183 `GD3O<rep>`, `GD3O<rep>T` and `GD3O<rep>Rc<k>` modules, 34.4 MB; the main module `GD3O1` of representative 1, which the regeneration also does not produce, is shipped as well) have their modules shipped as files in `lean/`, because the generators do not reproduce them byte for byte: they come from the big-representative and critical-leaf chains (265 and 304; rep 304 holds the eight critical leaves) and from an earlier run with 64-record chunks (the other six), and a rerun of `l5s4o` on them gives different files. What is reproducible by script is all other `GD3O*` modules (a full regeneration compared 7,051 `GD3O*` files, 0 different) and all 1,053 `LinRQSC*` modules; the eight representatives are not regenerated, and their files are checked only against the sha256 values in `MANIFEST.tsv` (the Lean kernel re-checks their content in a build).
5. **Planted-`sorry` controls.** The development tree keeps some planted-`sorry` control theorems in library modules that are not imported by the headline theorem and not shipped here; moving them out is a proposal (`repro/PROPOSAL_MOVE_CONTROLS.md`), not done.
6. **Edited comments.** To make the repository readable, comments in 31 hand-written Lean modules (references to internal working documents) and in some generator sources and scripts (path prefixes, internal labels) were edited before release. The files that were built are identical to the shipped ones except for these comments and path constants: the Lean declarations, tactics and terms (the kernel content) are unchanged, but the shipped files are not byte-identical to the files from which the development tree was built, and `MANIFEST.tsv` and `CHECKSUMS.sha256` carry the hashes of the files as shipped. Generated modules keep historical step labels in their headers.
7. **Provenance.** The Lean modules, Rust generators and the first draft of the paper were produced by an AI system (Claude, Anthropic); fresh sessions of the same system reviewed them; the questions, directions and the decision to formalize this statement came from Vico Bonfioli. The Lean kernel, not a human referee, checks the proofs.
8. **State of the repository and of the kernel check.** The repository state is the incrementally built development tree (comments aside, see item 6): no from-scratch rebuild of this public archive has been run yet. A rebuild is planned; it needs about 37 hours of Lean time on a machine with about 24 GB. The kernel check and the axiom output reported here refer to the development tree, not to a build of the shipped archive.

## File map

| path | content |
|---|---|
| `paper/main.tex`, `paper/main.pdf`, `paper/snippets/` | the paper |
| `lean/` | Lake project: `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, and `LRSpectrumFull/` with the 9,496 modules of the closure of `L5S5/FiveSpeedFinal4.lean` that are shipped (72.8 MB; the closure has 17,598; the other 8,102 regenerable generated modules, 635.1 MB, are listed with sha256 in `repro/MANIFEST.tsv` and restored by `repro/regen_data.sh`). No aggregator module exists; build by module name as `repro/build.sh` does |
| `repro/` | reproduction entry point: `build.sh`, `check_axioms.sh/.lean`, `regen_data.sh`, `MANIFEST.tsv` (module order, sha256, kind, generator), `generators/` (Rust sources), `inputs/`, `tools/`, `expected_output/`, `PROPOSAL_MOVE_CONTROLS.md`, `README.md` |
| `CHECKSUMS.sha256` | sha256 of every file of this repository (except itself) |
| `CITATION.cff`, `.zenodo.json`, `LICENSE.md` | citation and archive metadata, license |

## Citation

See `CITATION.cff`. Please cite the paper title above, Vico Bonfioli, version 1.0.1.
