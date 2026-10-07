import Lax458700Proofs.Comparability
import Mathlib.Order.Basic

/-!
# Permutation graphs

A permutation graph is represented by two linear orders on the same vertices. Two distinct
vertices are adjacent exactly when the orders place them in opposite orders. Geometrically,
the two orders give the endpoints on two parallel lines, and adjacency means that the
corresponding segments cross.

This module also proves that every permutation graph and its complement are comparability
graphs. The graph is oriented by inversions of the two orders; its complement is oriented
by pairs on which the orders agree.
-/

namespace Lax458700Proofs

universe u

variable {V : Type u}

/-- The strict relation consisting of the inversions between two linear orders. -/
def inversionRelation (first second : LinearOrder V) : V → V → Prop :=
  fun u v ↦ first.lt u v ∧ second.lt v u

/-- The strict relation consisting of pairs on which two linear orders agree. -/
def agreementRelation (first second : LinearOrder V) : V → V → Prop :=
  fun u v ↦ first.lt u v ∧ second.lt u v

/-- The permutation graph represented by two linear orders. Its edges are the pairs whose
relative order is reversed between `first` and `second`. -/
def permutationGraph (first second : LinearOrder V) : SimpleGraph V :=
  SimpleGraph.fromRel (inversionRelation first second)

set_option backward.inferInstanceAs.wrap.reuseSubInstances false in
/-- The opposite of a supplied linear order, kept on the same underlying type. -/
@[instance_reducible]
def oppositeLinearOrder (order : LinearOrder V) : LinearOrder V :=
  let _ : LinearOrder V := order
  inferInstanceAs (LinearOrder (OrderDual V))

/-- A pair of linear orders representing a fixed permutation graph. -/
structure PermutationRepresentation (G : SimpleGraph V) where
  /-- The order of the endpoints on the first line. -/
  firstOrder : LinearOrder V
  /-- The order of the endpoints on the second line. -/
  secondOrder : LinearOrder V
  /-- Pairs appear as edges exactly when the two orders disagree. -/
  underlying : permutationGraph firstOrder secondOrder = G

/-- A graph is a permutation graph if it has a representation by two linear orders. -/
def IsPermutationGraph (G : SimpleGraph V) : Prop :=
  Nonempty (PermutationRepresentation G)

@[simp]
theorem permutationGraph_adj (first second : LinearOrder V) (u v : V) :
    (permutationGraph first second).Adj u v ↔
      u ≠ v ∧
        ((first.lt u v ∧ second.lt v u) ∨ (first.lt v u ∧ second.lt u v)) :=
  Iff.rfl

/-- The inversion relation of two linear orders is a strict order. -/
theorem inversionRelation_isStrictOrder (first second : LinearOrder V) :
    IsStrictOrder V (inversionRelation first second) := by
  have hFirst : IsStrictOrder V first.lt := by
    let _ : LinearOrder V := first
    infer_instance
  have hSecond : IsStrictOrder V second.lt := by
    let _ : LinearOrder V := second
    infer_instance
  let _ : IsStrictOrder V first.lt := hFirst
  let _ : IsStrictOrder V second.lt := hSecond
  exact {
    irrefl := fun v h ↦ (irrefl_of first.lt v) h.1
    trans := fun _ _ _ huv hvw ↦
      ⟨_root_.trans huv.1 hvw.1, _root_.trans hvw.2 huv.2⟩
  }

/-- The agreement relation of two linear orders is a strict order. -/
theorem agreementRelation_isStrictOrder (first second : LinearOrder V) :
    IsStrictOrder V (agreementRelation first second) := by
  have hFirst : IsStrictOrder V first.lt := by
    let _ : LinearOrder V := first
    infer_instance
  have hSecond : IsStrictOrder V second.lt := by
    let _ : LinearOrder V := second
    infer_instance
  let _ : IsStrictOrder V first.lt := hFirst
  let _ : IsStrictOrder V second.lt := hSecond
  exact {
    irrefl := fun v h ↦ (irrefl_of first.lt v) h.1
    trans := fun _ _ _ huv hvw ↦
      ⟨_root_.trans huv.1 hvw.1, _root_.trans huv.2 hvw.2⟩
  }

/-- The inversions of two linear orders give a transitive orientation of their permutation
graph. -/
def permutationGraphOrientation (first second : LinearOrder V) :
    TransitiveOrientation (permutationGraph first second) where
  rel := inversionRelation first second
  isStrictOrder := inversionRelation_isStrictOrder first second
  underlying := rfl

/-- The pairs on which two linear orders agree form the complement of their permutation
graph. -/
theorem fromRel_agreementRelation_eq_compl_permutationGraph
    (first second : LinearOrder V) :
    SimpleGraph.fromRel (agreementRelation first second) =
      (permutationGraph first second)ᶜ := by
  have first_total {u v : V} (hne : u ≠ v) : first.lt u v ∨ first.lt v u := by
    let _ : LinearOrder V := first
    exact lt_or_gt_of_ne hne
  have second_total {u v : V} (hne : u ≠ v) : second.lt u v ∨ second.lt v u := by
    let _ : LinearOrder V := second
    exact lt_or_gt_of_ne hne
  have first_asymm {u v : V} (h : first.lt u v) : ¬first.lt v u := by
    let _ : LinearOrder V := first
    exact asymm h
  have second_asymm {u v : V} (h : second.lt u v) : ¬second.lt v u := by
    let _ : LinearOrder V := second
    exact asymm h
  ext u v
  rw [SimpleGraph.compl_adj]
  simp only [SimpleGraph.fromRel_adj, agreementRelation, permutationGraph,
    inversionRelation]
  constructor
  · rintro ⟨hne, ⟨hFirst, hSecond⟩ | ⟨hFirst, hSecond⟩⟩
    · refine ⟨hne, ?_⟩
      rintro ⟨_, ⟨_, hSecond'⟩ | ⟨hFirst', _⟩⟩
      · exact second_asymm hSecond hSecond'
      · exact first_asymm hFirst hFirst'
    · refine ⟨hne, ?_⟩
      rintro ⟨_, ⟨hFirst', _⟩ | ⟨_, hSecond'⟩⟩
      · exact first_asymm hFirst hFirst'
      · exact second_asymm hSecond hSecond'
  · rintro ⟨hne, hnot⟩
    rcases first_total hne with hFirst | hFirst <;>
      rcases second_total hne with hSecond | hSecond
    · exact ⟨hne, Or.inl ⟨hFirst, hSecond⟩⟩
    · exact (hnot ⟨hne, Or.inl ⟨hFirst, hSecond⟩⟩).elim
    · exact (hnot ⟨hne, Or.inr ⟨hFirst, hSecond⟩⟩).elim
    · exact ⟨hne, Or.inr ⟨hFirst, hSecond⟩⟩

/-- Reversing the second endpoint order turns crossings into non-crossings, and hence
represents the complement graph. -/
theorem permutationGraph_opposite_second (first second : LinearOrder V) :
    permutationGraph first (oppositeLinearOrder second) =
      (permutationGraph first second)ᶜ := by
  change SimpleGraph.fromRel (agreementRelation first second) =
    (permutationGraph first second)ᶜ
  exact fromRel_agreementRelation_eq_compl_permutationGraph first second

/-- Agreement of the two orders transitively orients the complement of a permutation
graph. -/
def permutationGraphComplementOrientation (first second : LinearOrder V) :
    TransitiveOrientation ((permutationGraph first second)ᶜ) where
  rel := agreementRelation first second
  isStrictOrder := agreementRelation_isStrictOrder first second
  underlying := fromRel_agreementRelation_eq_compl_permutationGraph first second

/-- Every permutation graph is a comparability graph. -/
theorem IsPermutationGraph.isComparabilityGraph {G : SimpleGraph V}
    (hG : IsPermutationGraph G) : IsComparabilityGraph G := by
  rcases hG with ⟨representation⟩
  rw [← representation.underlying]
  exact IsTransitivelyOrderable.isComparabilityGraph
    ⟨permutationGraphOrientation representation.firstOrder representation.secondOrder⟩

/-- The complement of every permutation graph is also a comparability graph. -/
theorem IsPermutationGraph.compl_isComparabilityGraph {G : SimpleGraph V}
    (hG : IsPermutationGraph G) : IsComparabilityGraph Gᶜ := by
  rcases hG with ⟨representation⟩
  rw [← representation.underlying]
  exact IsTransitivelyOrderable.isComparabilityGraph
    ⟨permutationGraphComplementOrientation representation.firstOrder
      representation.secondOrder⟩

/-- Permutation graphs are closed under graph complementation. -/
theorem IsPermutationGraph.compl {G : SimpleGraph V}
    (hG : IsPermutationGraph G) : IsPermutationGraph Gᶜ := by
  rcases hG with ⟨representation⟩
  refine ⟨{
    firstOrder := representation.firstOrder
    secondOrder := oppositeLinearOrder representation.secondOrder
    underlying := ?_
  }⟩
  rw [permutationGraph_opposite_second, representation.underlying]

/-- Thus permutation graphs are both comparability and cocomparability graphs. -/
theorem IsPermutationGraph.comparability_and_compl_comparability {G : SimpleGraph V}
    (hG : IsPermutationGraph G) :
    IsComparabilityGraph G ∧ IsComparabilityGraph Gᶜ :=
  ⟨hG.isComparabilityGraph, hG.compl_isComparabilityGraph⟩

end Lax458700Proofs
