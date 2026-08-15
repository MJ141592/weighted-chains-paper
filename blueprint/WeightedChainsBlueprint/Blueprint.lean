import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import WeightedChainsBlueprint.Chapters.Introduction
import WeightedChainsBlueprint.Chapters.Preliminaries
import WeightedChainsBlueprint.Chapters.Strategy
import WeightedChainsBlueprint.Chapters.DOne
import WeightedChainsBlueprint.Chapters.DTwo
import WeightedChainsBlueprint.Chapters.Conclusions
import WeightedChainsBlueprint.Chapters.Appendices

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Weighted chains: paper-to-Lean blueprint" =>

This companion records the exact correspondence between the conventional
mathematical paper and its kernel-checked Lean 4 formalisation. The paper
remains the authoritative human-readable manuscript; this site exposes the
associated declarations, their elaborated signatures, dependencies, proof
status, and commit-pinned source locations.

Every entry is currently marked *semantic-review-pending*. A completed Lean
proof establishes its formal statement, while the separate claim that the
formal statement faithfully expresses the paper requires author review. The
labels *direct*, *corrected*, *factored*, and *encoding* describe the present
shape of that correspondence and do not replace that review.

{include 0 WeightedChainsBlueprint.Chapters.Introduction}
{include 0 WeightedChainsBlueprint.Chapters.Preliminaries}
{include 0 WeightedChainsBlueprint.Chapters.Strategy}
{include 0 WeightedChainsBlueprint.Chapters.DOne}
{include 0 WeightedChainsBlueprint.Chapters.DTwo}
{include 0 WeightedChainsBlueprint.Chapters.Conclusions}
{include 0 WeightedChainsBlueprint.Chapters.Appendices}

{blueprint_graph (direction := LR) (preview := pinned)}

{blueprint_summary}
