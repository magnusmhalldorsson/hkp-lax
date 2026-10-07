import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.Chain
import Mathlib.Logic.Relation

/-!
---
title: Semi-transitive orientations
type: definition
---
A semi-transitive orientation is an acyclic orientation with no shortcut.
If a vertex-simple directed path with at least four vertices has an arc from
its first to its last vertex, every earlier vertex on that path must have an arc
to every later vertex. Forgetting arc directions recovers the graph.
-/

namespace Lax458700.Orientations

universe u
variable {V : Type u}

/-- Acyclicity, the underlying graph, and the absence of shortcuts. -/
def IsSemiTransitiveOrientation (G : SimpleGraph V) (rel : V → V → Prop) : Prop :=
  (∀ vertex : V, ¬Relation.TransGen rel vertex vertex) ∧
    SimpleGraph.fromRel rel = G ∧
    ∀ (vertices : List V) (hne : vertices ≠ []),
      vertices.Nodup → vertices.IsChain rel → 4 ≤ vertices.length →
      rel (vertices.head hne) (vertices.getLast hne) → vertices.Pairwise rel

def IsSemiTransitivelyOrientable (G : SimpleGraph V) : Prop :=
  ∃ rel : V → V → Prop, IsSemiTransitiveOrientation G rel

end Lax458700.Orientations
