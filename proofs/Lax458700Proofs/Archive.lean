import Lax458700.CliqueBound
import Lax458700Proofs.HKPBound

/-!
Bridges from the original constructive development to the public Lax definitions.
The copied proof modules have been renamed, not assumed as axioms.
-/

namespace Lax458700Proofs

universe u
variable {V : Type u}

theorem representation_public [DecidableEq V] {G : SimpleGraph V}
    (representation : WordRepresentation G) :
    Lax458700.Words.Represents G representation.word := by
  refine ⟨representation.covers, ?_⟩
  intro x y
  change G.Adj x y ↔ LettersAlternate representation.word x y
  exact (Iff.of_eq (congrArg (fun graph : SimpleGraph V ↦ graph.Adj x y)
    representation.underlying).symm).trans
      (alternationGraph_adj representation.word x y)

def representation_from_public [DecidableEq V] {G : SimpleGraph V}
    (word : List V) (h : Lax458700.Words.Represents G word) :
    WordRepresentation G :=
  { word := word
    covers := h.1
    underlying := by
      ext x y
      rw [alternationGraph_adj]
      exact (h.2 x y).symm }

theorem orientation_public {G : SimpleGraph V}
    (orientation : SemiTransitiveOrientation G) :
    Lax458700.Orientations.IsSemiTransitiveOrientation G orientation.rel := by
  refine ⟨orientation.acyclic, orientation.underlying, ?_⟩
  intro vertices hne hnodup hfollows hlen hedge
  exact orientation.complete_of_shortcut
    ⟨vertices, hne, hnodup, hfollows⟩ hlen hedge

def orientation_from_public {G : SimpleGraph V}
    (rel : V → V → Prop)
    (h : Lax458700.Orientations.IsSemiTransitiveOrientation G rel) :
    SemiTransitiveOrientation G :=
  { rel := rel
    acyclic := h.1
    underlying := h.2.1
    complete_of_shortcut := fun path ↦
      h.2.2 path.vertices path.nonempty path.nodup path.follows }

/--
---
conclusion: Lax458700.WordToOrientation.wordToOrientation
---
Orient edges by first appearances in a representing word; the occurrence
argument rules out shortcuts even for nonuniform words.
-/
theorem wordToOrientation {V : Type u} [DecidableEq V] (G : SimpleGraph V) :
    Lax458700.Words.IsWordRepresentable G →
      Lax458700.Orientations.IsSemiTransitivelyOrientable G := by
  rintro ⟨word, hword⟩
  let representation := representation_from_public word hword
  have hG : IsWordRepresentable G := ⟨representation⟩
  obtain ⟨orientation⟩ := hG.isSemiTransitivelyOrientable
  exact ⟨orientation.rel, orientation_public orientation⟩

/--
---
conclusion: Lax458700.OrientationToWord.orientationToUniformWord
---
The finite string-digraph construction separates each nonedge while preserving
the common alternating phase of all arcs.
-/
theorem orientationToUniformWord {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    Lax458700.Orientations.IsSemiTransitivelyOrientable G →
      ∃ k : ℕ, Lax458700.Words.HasUniformRepresentation G k := by
  rintro ⟨rel, hrel⟩
  let orientation := orientation_from_public rel hrel
  let representation := orientation.toUniformWordRepresentation
  exact ⟨representation.multiplicity, representation.representation.word,
    representation_public representation.representation,
    representation.multiplicity_pos, representation.uniform⟩

/--
---
conclusion: Lax458700.Characterization.wordRepresentable_iff_semiTransitivelyOrientable
assumptions:
  - Lax458700.WordToOrientation.wordToOrientation
  - Lax458700.OrientationToWord.orientationToUniformWord
---
Combine the independently proved forward implication and the finite uniform converse.
-/
theorem characterization {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    Lax458700.Words.IsWordRepresentable G ↔
      Lax458700.Orientations.IsSemiTransitivelyOrientable G := by
  constructor
  · exact Lax458700.WordToOrientation.wordToOrientation G
  · intro hG
    obtain ⟨k, word, hrep, _, _⟩ :=
      Lax458700.OrientationToWord.orientationToUniformWord G hG
    exact ⟨word, hrep⟩

/--
---
conclusion: Lax458700.CliqueBound.uniformRepresentation_cliqueBound
assumptions:
  - Lax458700.WordToOrientation.wordToOrientation
---
Use a semi-transitive orientation and the corrected two-occurrence HKP blocks
for the complement of a maximum clique.
-/
theorem cliqueBound {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    Lax458700.Words.IsWordRepresentable G → G ≠ ⊤ →
      Lax458700.Words.HasUniformRepresentation G
        (2 * (Fintype.card V - G.cliqueNum)) := by
  intro hG hneTop
  obtain ⟨rel, hrel⟩ := Lax458700.WordToOrientation.wordToOrientation G hG
  have hnative : IsSemiTransitivelyOrientable G :=
    ⟨orientation_from_public rel hrel⟩
  obtain ⟨representation, hmult⟩ :=
    hnative.exists_uniformWordRepresentation_cliqueBound hneTop
  rw [← hmult]
  exact ⟨representation.representation.word,
    representation_public representation.representation,
    representation.multiplicity_pos, representation.uniform⟩

end Lax458700Proofs
