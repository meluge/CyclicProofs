# Thesis / paper draft for CyclicTactic

Initial draft documenting the work done up to the §6 emission canonical
form, in preparation for thesis-scale writing.

## Structure

```
thesis/
├── main.tex                        — document root + \input{chapters/...}
├── preamble.tex                    — packages, theorem envs, Lean lstlistings
├── bibliography.bib                — papers referenced in the draft
└── chapters/
    ├── 01-introduction.tex         — motivation, contributions, outline
    ├── 02-background.tex           — cyclic proofs, SCT, Grotenhuis-Otten §5–6
    ├── 03-architecture.tex         — surface tactics, side-channel, two-phase elab
    ├── 04-implementation.tex       — §5 annotation, §6 augmentation/emission, mutual
    ├── 05-evaluation.tex           — example suite, Cyclist comparison
    └── 06-limitations-and-future.tex — gaps, the WF and Löb extensions, DAG discussion
```

## Building

Standard `pdflatex` + `bibtex` (article class, no exotic packages):

```
cd thesis
pdflatex main && bibtex main && pdflatex main && pdflatex main
```

Or with `latexmk`:
```
cd thesis
latexmk -pdf main.tex
```

## State of the draft

The current draft documents what has been built. It does **not** yet
include:

- A full proof of the conjectural dispatch characterisation theorem in
  §6.3 of the limitations chapter (that's the algorithmic content the
  WF / Löb branches are working toward).
- A figure for the two-phase elaboration flow (the structure is
  described in prose; converting to a tikz diagram is a TODO).
- Empirical numbers for §5.4 "Code-size and elaboration overhead"
  (currently a placeholder; needs systematic measurement).
- Detailed worked examples in §5 (currently summarised; one
  end-to-end Ackermann example would be a useful addition).
- A conclusion chapter (the limitations chapter currently doubles as
  the closing material; a proper §7 conclusion + abstract refinement
  would be welcome).

## Cross-references to the code

Throughout the draft we cite specific Lean files in the repository. The
references assume the layout established after the `clean up after
merging` commit:

- `CyclicTactic/Tactic.lean` — surface tactics + `cyclic_thm` /
  `cyclic_mutual` commands.
- `CyclicTactic/Build.lean` — event types, tree builder, SortInfo.
- `CyclicTactic/ProofTree.lean` — data-DSL `ProofTree`, SCG extraction.
- `CyclicTactic/SizeChange.lean` — SCT closure + idempotent check.
- `CyclicTactic/PaperAnnotation.lean` — §5 annotation + Lemma 5.9.
- `CyclicTactic/Theorem6.lean` — §6 augmentation + emission.
- `CyclicTactic/EmitCommon.lean` — shared script utilities.
- `CyclicTactic/Examples/` — worked-example suite (Smoke, Probe, Probe2,
  drp, MutualSmoke, MergeSort, CyclistComparison).
- `papers/` — referenced PDFs with legible Author-Year filenames.
