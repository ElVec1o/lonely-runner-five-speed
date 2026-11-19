# PROPOSAL (not applied): move the planted-sorry controls out of importable library modules

Status: PROPOSAL ONLY (not applied). Nothing in the closure of the headline theorem is affected.

## What was found (closure from `MANIFEST.tsv`, `tools/source_scan.sh`, `expected_output/planted_controls*.txt`)

* Some library modules of the development tree (`L5S4.T2D<k>`, `T2All`, `T2Final`, `GT2` via `T2D<k>Pos`) carry planted `ctl_sorry` controls; moving them to modules that nothing imports is the natural hygiene step.
* Parsing `import` lines from `FiveSpeedFinal4` downward gives a closure of 17,598 modules. **None of the 48 control-bearing files below is in it**, and the stripped source of the 17,598 modules contains no `sorry` token at all (0 lines). The headline chain imports the generated mirror modules `AggFive.Clean.T2*` (22 `T2D<k>`, 22 `T2D<k>Pos`, 4 `T2E<k>`, 4 `T2E<k>Pos`, `T2All`, `T2Final`), which carry no control. So the headline does not depend on the planted controls, and `check_axioms.sh` shows `sorryAx` only for its own two scratch controls.
* The 48 files remain importable library modules. Anyone who imports `L5S4.T2D<k>` (or builds the whole library with a default target) gets a `sorryAx`-carrying constant into the environment and a `declaration uses sorry` warning. That is a hygiene and honesty issue for a release, not a soundness issue for the headline.

## The 48 files (path relative to the `lean/` directory of the development tree; control line numbers in `expected_output/planted_controls_lines.txt`)

### A. dedicated scan/control modules (already separate; only a check that nothing in the closure imports them is needed): 11 files

* `LRSpectrumFull/AggFive/Ctl.lean`
* `LRSpectrumFull/L5Reg/RegCtl.lean`
* `LRSpectrumFull/L5Reg/RegPCtl.lean`
* `LRSpectrumFull/L5S4/GD3Ctl.lean`
* `LRSpectrumFull/L5S4/GFlatCtl.lean`
* `LRSpectrumFull/L5S4/LinAx.lean`
* `LRSpectrumFull/L5S4/LinRAx.lean`
* `LRSpectrumFull/L5S4/T2AxScan.lean`
* `LRSpectrumFull/L5S4/T2AxScan2.lean`
* `LRSpectrumFull/L5S5/FiveSpeedAxioms.lean`
* `LRSpectrumFull/L5S5/T5StoreCtl.lean`

### B. library modules that carry a control inside a module other modules import: 37 files

| file | imported by (non-control modules; none of them is in the closure) |
|---|---|
| `LRSpectrumFull/L5S4/GD3F3.lean` | - |
| `LRSpectrumFull/L5S4/GD3K5.lean` | - |
| `LRSpectrumFull/L5S4/GD3O2.lean` | - |
| `LRSpectrumFull/L5S4/GD3S5.lean` | - |
| `LRSpectrumFull/L5S4/GT2.lean` | - |
| `LRSpectrumFull/L5S4/T2All.lean` | `L5S4.T2FinalTest` |
| `LRSpectrumFull/L5S4/T2D0.lean` | `L5S4.T2D0Pos` |
| `LRSpectrumFull/L5S4/T2D1.lean` | `L5S4.T2D1Pos` |
| `LRSpectrumFull/L5S4/T2D10.lean` | `L5S4.T2D10Pos` |
| `LRSpectrumFull/L5S4/T2D11.lean` | `L5S4.T2D11Pos` |
| `LRSpectrumFull/L5S4/T2D12.lean` | `L5S4.T2D12Pos` |
| `LRSpectrumFull/L5S4/T2D13.lean` | `L5S4.T2D13Pos` |
| `LRSpectrumFull/L5S4/T2D14.lean` | `L5S4.T2D14Pos` |
| `LRSpectrumFull/L5S4/T2D15.lean` | `L5S4.T2D15Pos` |
| `LRSpectrumFull/L5S4/T2D16.lean` | `L5S4.T2D16Pos` |
| `LRSpectrumFull/L5S4/T2D17.lean` | `L5S4.T2D17Pos` |
| `LRSpectrumFull/L5S4/T2D18.lean` | `L5S4.T2D18Pos` |
| `LRSpectrumFull/L5S4/T2D2.lean` | `L5S4.T2D2Pos` |
| `LRSpectrumFull/L5S4/T2D20.lean` | `L5S4.T2D20Pos` |
| `LRSpectrumFull/L5S4/T2D21.lean` | `L5S4.T2D21Pos` |
| `LRSpectrumFull/L5S4/T2D22.lean` | `L5S4.T2D22Pos` |
| `LRSpectrumFull/L5S4/T2D23.lean` | `L5S4.T2D23Pos` |
| `LRSpectrumFull/L5S4/T2D24.lean` | `L5S4.T2D24Pos` |
| `LRSpectrumFull/L5S4/T2D25.lean` | `L5S4.T2D25Pos` |
| `LRSpectrumFull/L5S4/T2D3.lean` | `L5S4.T2D3Pos` |
| `LRSpectrumFull/L5S4/T2D4.lean` | `L5S4.T2D4Pos` |
| `LRSpectrumFull/L5S4/T2D6.lean` | `L5S4.T2D6Pos` |
| `LRSpectrumFull/L5S4/T2D7.lean` | `L5S4.T2D7Pos` |
| `LRSpectrumFull/L5S4/T2D8.lean` | `L5S4.T2D8Pos` |
| `LRSpectrumFull/L5S4/T2D9.lean` | `L5S4.T2D9Pos` |
| `LRSpectrumFull/L5S4/T2E1.lean` | `L5S4.T2E1Pos` |
| `LRSpectrumFull/L5S4/T2E13.lean` | `L5S4.T2E13Pos` |
| `LRSpectrumFull/L5S4/T2E19.lean` | `L5S4.T2E19Pos` |
| `LRSpectrumFull/L5S4/T2E5.lean` | `L5S4.T2E5Pos` |
| `LRSpectrumFull/L5S4/T2Final.lean` | - |
| `LRSpectrumFull/L5S4/T2Lead4.lean` | - |
| `LRSpectrumFull/L5S4/T2LinkReal.lean` | - |

Other importers of control-bearing modules (all inside the 48): `T2AxScan`, `T2AxScan2`, `FiveSpeedAxioms`, `T2Lead4` (imports `GT2`), `T2Final`/`T2All` (import `T2All`, `T2D<k>`), `T2FinalTest` (not control-bearing, imports `T2All`). `GD3O1`/`GD3O2` of the S4O library: `GD3O2` carries a control; the closure uses the renamed main modules `GD3OA1`, `GD3OA2` (modname.tsv) which have none.

## Plan (every step is checkable)
1. For each file in B: create `<Module>Ctl.lean` (new file, `import <Module>`) containing exactly the planted-control declaration(s) (`theorem ctl_sorry ...`, `#print axioms ctl_sorry`, any `#print axioms` of the real theorems that the control is meant to be compared with) moved verbatim, and delete those lines from the original. The generators that emit these files must be changed in the same step (otherwise a regeneration puts the control back): `l5s4r_gen` (T2D<k>, T2D<k>Pos), `l5s4s_gen` (T2E<k>), the T2All/T2Final assembly (`l5s4s_gen` or hand), and the hand-written `GT2`, `GD3F3`, `GD3K5`, `GD3S5`, `GD3O2`, `T2Lead4`, `T2LinkReal`. `l5_agg`'s Clean mirror (which strips the control from a copy) then becomes byte-identical to the original and can be dropped later; do not drop it in the same step.
2. Rebuild only the affected modules (the 37 B files, their 29 non-control importers: 28 `T2D<k>Pos`/`T2E<k>Pos` and `T2FinalTest`; the 11 A files only if edited), one at a time through `build.sh --only`, then the new `*Ctl` modules. Cost: not measured; the T2 per-node chains were the heavier part of the S4R/S4S stages (several GB each), estimate a few hours, ESTIMATE only.
3. Acceptance: (a) `bash tools/make_manifest.sh` gives a MANIFEST.tsv with the same 17,598 sha256 values (the closure is untouched, so every hash and every olean of the closure stays as it is); (b) `bash check_axioms.sh` still prints PASS; (c) `grep -rl "by sorry" lean/LRSpectrumFull` outside the `*Ctl*`/`*Ax*` modules returns nothing; (d) the new `*Ctl` modules print `sorryAx`.
4. Risks: the generators (`l5s4r_gen`, `l5s4s_gen`) have hard-coded output paths and stage-specific state; editing them requires regenerating at least one node (e.g. T2D1) and comparing with the tree before touching the rest. The closure is not affected, so this can be done after a release; it must be done before any claim of the form "the library contains no sorry".

## What this does NOT change
The headline theorems, their axioms, MANIFEST.tsv and the bundle contents. Until the proposal is executed the bundle ships only the closure modules, none of which contains a control (the 48 files are not part of `lean/`).
