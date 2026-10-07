import Lax458700.WordToOrientation
import Lax458700.OrientationToWord

/-!
---
title: The HKP characterization of finite word-representable graphs
type: theorem
---
A finite graph is word-representable if and only if it admits a semi-transitive
orientation. Here word-representability permits nonuniform words.
-/

namespace Lax458700.Characterization

universe u

axiom wordRepresentable_iff_semiTransitivelyOrientable
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
  Lax458700.Words.IsWordRepresentable G ↔
    Lax458700.Orientations.IsSemiTransitivelyOrientable G

end Lax458700.Characterization
