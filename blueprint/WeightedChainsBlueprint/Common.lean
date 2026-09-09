import VersoBlueprint
import WeightedChainsBlueprint.PaperSources

namespace WeightedChainsBlueprint

/-- Provenance for a statement in the journal manuscript.

`label` is the blueprint label of the node, which `main.tex` carries either as
`\label{…}` inside a theorem-like environment or as a pair of
`% blueprint-begin: …` / `% blueprint-end: …` comment lines.  The one-based,
inclusive line range is looked up in `paperSpans`, which
`blueprint/scripts/paper_sources.py` generates from `main.tex` before every
build, so the blueprint never hard-codes line numbers of the paper.  An
unknown label yields a reference without spans, which `generate-redirects.py`
rejects. -/
def paperSource (label paperRef : String) : Informal.Source.Ref := {
  document := "paper-source"
  spans :=
    match paperSpans.lookup label with
    | some (startLine, endLine) =>
      #[{
        page := paperRef
        text := some {
          path := "../main.tex"
          startLine := startLine
          endLine := endLine
        }
      }]
    | none => #[]
}

end WeightedChainsBlueprint
