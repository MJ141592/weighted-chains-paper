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

This companion links each statement of the paper to its kernel-checked Lean 4
formalisation. For every definition, lemma and theorem it shows the associated
Lean declarations with their elaborated signatures, the dependency graph, the
lines of the manuscript where the statement appears, and commit-pinned links to
the Lean source. Where the Lean encoding of a statement differs in form from
the paper, the entry says how.

{include 0 WeightedChainsBlueprint.Chapters.Introduction}
{include 0 WeightedChainsBlueprint.Chapters.Preliminaries}
{include 0 WeightedChainsBlueprint.Chapters.Strategy}
{include 0 WeightedChainsBlueprint.Chapters.DOne}
{include 0 WeightedChainsBlueprint.Chapters.DTwo}
{include 0 WeightedChainsBlueprint.Chapters.Conclusions}
{include 0 WeightedChainsBlueprint.Chapters.Appendices}

{blueprint_graph (direction := LR) (preview := pinned)}

{blueprint_summary}
