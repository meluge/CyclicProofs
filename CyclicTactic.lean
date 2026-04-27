-- This module serves as the root of the `CyclicTactic` library.
--
-- A fork of `Cyclic` carrying just the theoretical machinery (SCT,
-- proof trees, trace extraction, reset annotation, reorganisation,
-- Wehr 3.2.4 induction-order, structural emission). The plan is to
-- rebuild the surface language as actual Lean tactics — `cycCases`,
-- `cycBack`, etc. that manipulate goal state — with the cyclic
-- structure recorded into a side-channel for SCT validation. See
-- `Cyclic/` for the original data-DSL approach.
import CyclicTactic.SizeChange
import CyclicTactic.Extract
import CyclicTactic.Measure
import CyclicTactic.ProofTree
import CyclicTactic.InductionOrder
import CyclicTactic.Annotation
import CyclicTactic.Reorganize
import CyclicTactic.Unravel
import CyclicTactic.Build
import CyclicTactic.Tactic
import CyclicTactic.Examples.Smoke
import CyclicTactic.Examples.Probe
import CyclicTactic.Examples.Probe2
import CyclicTactic.Examples.drp
