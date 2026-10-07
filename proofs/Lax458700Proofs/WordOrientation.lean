import Lax458700Proofs.SemiTransitive
import Lax458700Proofs.Word
import Mathlib.Data.List.Basic

/-!
# Orienting a graph from a representing word

For a word representation, orient every edge from the letter whose first occurrence is
earlier to the letter whose first occurrence is later. This module proves that the result
is an acyclic orientation of the represented graph.

The remaining combinatorial step for the forward characterization is isolated as the
path-closure obligation in `WordRepresentation.firstOccurrenceSemiTransitiveOrientation`.
For a uniform representing word, this follows by interleaving corresponding occurrences
of letters along a directed path.
-/

namespace Lax458700Proofs

universe u

variable {V : Type u} [DecidableEq V]

namespace Word

/-- In a covering word, distinct letters have distinct first-occurrence positions. -/
theorem Covers.idxOf_injective {word : Word V} (covers : word.Covers) :
    Function.Injective word.idxOf := by
  intro left right heq
  have hLeft : word.idxOf left < word.length :=
    List.idxOf_lt_length_of_mem (covers left)
  have hRight : word.idxOf right < word.length :=
    List.idxOf_lt_length_of_mem (covers right)
  change word.idxOf left = word.idxOf right at heq
  calc
    left = word[word.idxOf left] := (List.getElem_idxOf hLeft).symm
    _ = word[word.idxOf right] :=
      congrArg word.get (Fin.ext heq)
    _ = right := List.getElem_idxOf hRight

end Word

namespace WordRepresentation

/-- The first-occurrence orientation relation of a representing word. -/
def firstOccurrenceRel {G : SimpleGraph V} (representation : WordRepresentation G) :
    V → V → Prop :=
  fun left right ↦ G.Adj left right ∧
    representation.word.idxOf left < representation.word.idxOf right

/-- Forgetting the directions in the first-occurrence relation recovers the represented
graph. -/
theorem fromRel_firstOccurrenceRel {G : SimpleGraph V}
    (representation : WordRepresentation G) :
    SimpleGraph.fromRel representation.firstOccurrenceRel = G := by
  ext left right
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h.1
    · exact h.1.symm
  · intro hedge
    have hne : left ≠ right := fun h ↦ G.loopless.irrefl left (h ▸ hedge)
    have hidx : representation.word.idxOf left ≠ representation.word.idxOf right :=
      fun h ↦ hne (representation.covers.idxOf_injective h)
    rcases Nat.lt_or_gt_of_ne hidx with hlt | hgt
    · exact ⟨hne, Or.inl ⟨hedge, hlt⟩⟩
    · exact ⟨hne, Or.inr ⟨hedge.symm, hgt⟩⟩

/-- Orient every represented edge from its earlier first occurrence to its later one. -/
def firstOccurrenceOrientation {G : SimpleGraph V}
    (representation : WordRepresentation G) : AcyclicOrientation G where
  rel := representation.firstOccurrenceRel
  acyclic := fun vertex cycle ↦ by
    have hcycle :
        Relation.TransGen (· < ·)
          (representation.word.idxOf vertex) (representation.word.idxOf vertex) :=
      cycle.lift representation.word.idxOf (fun _ _ hedge ↦ hedge.2)
    have hlt : representation.word.idxOf vertex < representation.word.idxOf vertex := by
      simpa only [Relation.transGen_eq_self] using hcycle
    exact (Nat.lt_irrefl _ hlt)
  underlying := representation.fromRel_firstOccurrenceRel

/-- A word representation is enough to give the represented graph an acyclic orientation. -/
theorem isAcyclicallyOrientable {G : SimpleGraph V}
    (representation : WordRepresentation G) : Nonempty (AcyclicOrientation G) :=
  ⟨representation.firstOccurrenceOrientation⟩

/-- Package the first-occurrence orientation as semi-transitive once its standard path
closure lemma has been supplied. This states the exact remaining proof obligation for the
forward direction of the characterization. -/
def firstOccurrenceSemiTransitiveOrientation {G : SimpleGraph V}
    (representation : WordRepresentation G)
    (complete : ∀ path : DirectedPath representation.firstOccurrenceRel,
      4 ≤ path.vertices.length →
      representation.firstOccurrenceRel path.start path.finish →
      path.IsTransitivelyClosed) : SemiTransitiveOrientation G where
  toAcyclicOrientation := representation.firstOccurrenceOrientation
  complete_of_shortcut := complete

end WordRepresentation

end Lax458700Proofs
