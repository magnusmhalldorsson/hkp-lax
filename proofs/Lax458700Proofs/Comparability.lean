import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.RelClasses

/-!
# Comparability graphs

This module defines the comparability graph of a partial order and a transitive
orientation of a simple graph.  Its main theorem proves the classical characterization:
a graph is a comparability graph if and only if it admits a transitive orientation.
-/

namespace Lax458700Proofs

universe u

variable {V : Type u}

/-- The comparability graph of a partial order: two distinct vertices are adjacent when
they are comparable in the order. -/
def comparabilityGraph (P : PartialOrder V) : SimpleGraph V :=
  SimpleGraph.fromRel P.le

/-- A graph is a comparability graph if it is the comparability graph of some partial order
on its vertex type. -/
def IsComparabilityGraph (G : SimpleGraph V) : Prop :=
  ∃ P : PartialOrder V, comparabilityGraph P = G

/-- A transitive orientation of `G` is a strict order whose undirected graph is `G`.

The strict-order relation records the directions of the edges.  Its transitivity says that
whenever `u → v` and `v → w`, the edge `u → w` is also present. -/
structure TransitiveOrientation (G : SimpleGraph V) where
  /-- The directed edge relation. -/
  rel : V → V → Prop
  /-- The directed edge relation is irreflexive and transitive. -/
  isStrictOrder : IsStrictOrder V rel
  /-- Forgetting edge directions recovers the original graph. -/
  underlying : SimpleGraph.fromRel rel = G

/-- A graph is transitively orderable if it has a transitive orientation. -/
def IsTransitivelyOrderable (G : SimpleGraph V) : Prop :=
  Nonempty (TransitiveOrientation G)

@[simp]
theorem comparabilityGraph_adj (P : PartialOrder V) (u v : V) :
    (comparabilityGraph P).Adj u v ↔ u ≠ v ∧ (P.le u v ∨ P.le v u) :=
  Iff.rfl

/-- The strict part of a partial order has the same underlying simple graph as the
non-strict order. -/
theorem fromRel_lt_eq_comparabilityGraph (P : PartialOrder V) :
    SimpleGraph.fromRel P.lt = comparabilityGraph P := by
  let _ : PartialOrder V := P
  ext u v
  simp only [SimpleGraph.fromRel_adj, comparabilityGraph_adj]
  constructor
  · exact fun ⟨hne, h⟩ ↦ ⟨hne, h.elim (Or.inl ∘ le_of_lt) (Or.inr ∘ le_of_lt)⟩
  · rintro ⟨hne, huv | hvu⟩
    · exact ⟨hne, Or.inl (lt_of_le_of_ne huv hne)⟩
    · exact ⟨hne, Or.inr (lt_of_le_of_ne hvu hne.symm)⟩

/-- Orient a comparability graph from smaller to larger in its defining partial order. -/
def TransitiveOrientation.ofPartialOrder (P : PartialOrder V) :
    TransitiveOrientation (comparabilityGraph P) := by
  let _ : PartialOrder V := P
  exact {
    rel := P.lt
    isStrictOrder := inferInstance
    underlying := fromRel_lt_eq_comparabilityGraph P
  }

/-- Reflexively close a transitive orientation to obtain its associated partial order. -/
@[instance_reducible]
def TransitiveOrientation.toPartialOrder {G : SimpleGraph V}
    (orientation : TransitiveOrientation G) : PartialOrder V :=
  @partialOrderOfSO V orientation.rel orientation.isStrictOrder

/-- The partial order associated to a transitive orientation has the original graph as
its comparability graph. -/
theorem TransitiveOrientation.comparabilityGraph_toPartialOrder {G : SimpleGraph V}
    (orientation : TransitiveOrientation G) :
    comparabilityGraph orientation.toPartialOrder = G := by
  calc
    comparabilityGraph orientation.toPartialOrder = SimpleGraph.fromRel orientation.rel := by
      ext u v
      change
        (u ≠ v ∧ ((u = v ∨ orientation.rel u v) ∨ (v = u ∨ orientation.rel v u))) ↔
          u ≠ v ∧ (orientation.rel u v ∨ orientation.rel v u)
      aesop
    _ = G := orientation.underlying

/-- A comparability graph admits the transitive orientation supplied by the strict part
of its defining partial order. -/
theorem IsComparabilityGraph.isTransitivelyOrderable {G : SimpleGraph V}
    (hG : IsComparabilityGraph G) : IsTransitivelyOrderable G := by
  rcases hG with ⟨P, rfl⟩
  exact ⟨TransitiveOrientation.ofPartialOrder P⟩

/-- A transitive orientation induces a partial order by reflexively closing its directed
edge relation; that order has `G` as its comparability graph. -/
theorem IsTransitivelyOrderable.isComparabilityGraph {G : SimpleGraph V}
    (hG : IsTransitivelyOrderable G) : IsComparabilityGraph G := by
  rcases hG with ⟨orientation⟩
  exact ⟨orientation.toPartialOrder, orientation.comparabilityGraph_toPartialOrder⟩

/-- **Comparability graph characterization.** A simple graph is a comparability graph if
and only if its edges can be oriented transitively. -/
theorem isComparabilityGraph_iff_isTransitivelyOrderable (G : SimpleGraph V) :
    IsComparabilityGraph G ↔ IsTransitivelyOrderable G :=
  ⟨IsComparabilityGraph.isTransitivelyOrderable,
    IsTransitivelyOrderable.isComparabilityGraph⟩

/-- An equivalent formulation of the characterization that exposes the orientation
object directly. -/
theorem isComparabilityGraph_iff_nonempty_transitiveOrientation (G : SimpleGraph V) :
    IsComparabilityGraph G ↔ Nonempty (TransitiveOrientation G) :=
  isComparabilityGraph_iff_isTransitivelyOrderable G

end Lax458700Proofs
