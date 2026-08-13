import VersoBlueprint

namespace WeightedChainsBlueprint

/-- Provenance for a statement in the journal manuscript. Line numbers are
one-based and inclusive, matching `main.tex` at the artifact commit. -/
def paperSource (paperRef : String) (startLine endLine : Nat) :
    Informal.Source.Ref := {
  document := "paper-source"
  spans := #[{
    page := paperRef
    text := some {
      path := "../main.tex"
      startLine := startLine
      endLine := endLine
    }
  }]
}

end WeightedChainsBlueprint
