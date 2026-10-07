import Lax458700.Words
import Lax458700.Orientations

/-!
---
title: Finite semi-transitive orientations admit uniform words
type: theorem
---
Every finite graph with a semi-transitive orientation admits a positive uniform
word representation. The construction uses topological orders of a string digraph
and concatenates words that separate the nonedges.
-/

namespace Lax458700.OrientationToWord

universe u

axiom orientationToUniformWord {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
  Lax458700.Orientations.IsSemiTransitivelyOrientable G →
    ∃ k : ℕ, Lax458700.Words.HasUniformRepresentation G k

end Lax458700.OrientationToWord
