import Lax458700.Words
import Lax458700.Orientations

/-!
---
title: Word representations induce semi-transitive orientations
type: theorem
---
Every word-representable graph has a semi-transitive orientation.
This direction does not require the vertex type to be finite.
-/

namespace Lax458700.WordToOrientation

universe u

axiom wordToOrientation {V : Type u} [DecidableEq V] (G : SimpleGraph V) :
  Lax458700.Words.IsWordRepresentable G →
    Lax458700.Orientations.IsSemiTransitivelyOrientable G

end Lax458700.WordToOrientation
