import Lax458700Proofs.GeneralWordOrientation
import Lax458700Proofs.StringDigraph

/-!
# The finite converse characterization

This module concatenates the local two-uniform separator words. Every block has the
same exact `left right left right` restriction on an oriented edge, so edges continue
to alternate across block boundaries. Every distinct nonedge has a dedicated block in
which it fails to alternate. A canonical base block handles coverage and the complete
graph case.
-/

namespace Lax458700Proofs

universe u

variable {V : Type u}

/-- Ordered pairs of distinct nonadjacent vertices. Using ordered pairs introduces
harmless duplication but avoids choosing representatives of unordered pairs. -/
def DistinctNonedge (G : SimpleGraph V) :=
  {pair : V × V // pair.1 ≠ pair.2 ∧ ¬G.Adj pair.1 pair.2}

namespace SemiTransitiveOrientation

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The local separator selected for one ordered nonedge. -/
noncomputable def separatorWord (orientation : SemiTransitiveOrientation G)
    (pair : DistinctNonedge G) : Word V :=
  Classical.choose
    (orientation.exists_two_uniform_separating_word_of_nonedge
      pair.property.1 pair.property.2)

theorem separatorWord_uniform (orientation : SemiTransitiveOrientation G)
    (pair : DistinctNonedge G) :
    (orientation.separatorWord pair).IsUniform 2 :=
  (Classical.choose_spec
    (orientation.exists_two_uniform_separating_word_of_nonedge
      pair.property.1 pair.property.2)).1

theorem separatorWord_edgePattern (orientation : SemiTransitiveOrientation G)
    (pair : DistinctNonedge G) {left right : V}
    (hne : left ≠ right) (hedge : orientation.rel left right) :
    (orientation.separatorWord pair).restrictToPair left right =
      alternatingPairs left right 2 :=
  (Classical.choose_spec
    (orientation.exists_two_uniform_separating_word_of_nonedge
      pair.property.1 pair.property.2)).2.1 hne hedge

theorem separatorWord_separates (orientation : SemiTransitiveOrientation G)
    (pair : DistinctNonedge G) :
    ¬LettersAlternate (orientation.separatorWord pair) pair.val.1 pair.val.2 :=
  (Classical.choose_spec
    (orientation.exists_two_uniform_separating_word_of_nonedge
      pair.property.1 pair.property.2)).2.2

/-- A canonical two-uniform block preserving all oriented edges. -/
noncomputable def baseWord (orientation : SemiTransitiveOrientation G) : Word V :=
  StringTopologicalListing.erasedWord
    (StringTopologicalListing.ofAcyclic (t := 2) orientation.acyclic)

theorem baseWord_uniform (orientation : SemiTransitiveOrientation G) :
    orientation.baseWord.IsUniform 2 :=
  StringTopologicalListing.erasedWord_uniform _

theorem baseWord_edgePattern (orientation : SemiTransitiveOrientation G)
    {left right : V} (hne : left ≠ right) (hedge : orientation.rel left right) :
    orientation.baseWord.restrictToPair left right = alternatingPairs left right 2 :=
  StringTopologicalListing.restrictToPair_eq_alternatingPairs_of_rel _ hne hedge

/-- The base block followed by one local separator for every ordered nonedge. -/
noncomputable def representationBlocks (orientation : SemiTransitiveOrientation G) :
    List (Word V) := by
  classical
  letI : Fintype (DistinctNonedge G) :=
    Fintype.ofInjective (fun pair : DistinctNonedge G ↦ pair.val) Subtype.val_injective
  exact orientation.baseWord ::
    (Finset.univ.toList.map orientation.separatorWord : List (Word V))

/-- The finite converse word, obtained by flattening all separator blocks. -/
noncomputable def representationWord (orientation : SemiTransitiveOrientation G) : Word V :=
  orientation.representationBlocks.flatten

theorem separatorWord_mem_representationBlocks
    (orientation : SemiTransitiveOrientation G) (pair : DistinctNonedge G) :
    orientation.separatorWord pair ∈ orientation.representationBlocks := by
  classical
  simp [representationBlocks]

theorem representationBlocks_uniform (orientation : SemiTransitiveOrientation G) :
    ∀ word ∈ orientation.representationBlocks, word.IsUniform 2 := by
  classical
  intro word hword
  simp only [representationBlocks, List.mem_cons, List.mem_map,
    Finset.mem_toList, Finset.mem_univ, true_and] at hword
  rcases hword with rfl | ⟨pair, rfl⟩
  · exact orientation.baseWord_uniform
  · exact orientation.separatorWord_uniform pair

theorem representationBlocks_edgePattern (orientation : SemiTransitiveOrientation G)
    {left right : V} (hne : left ≠ right) (hedge : orientation.rel left right) :
    ∀ word ∈ orientation.representationBlocks,
      word.restrictToPair left right = alternatingPairs left right 2 := by
  classical
  intro word hword
  simp only [representationBlocks, List.mem_cons, List.mem_map,
    Finset.mem_toList, Finset.mem_univ, true_and] at hword
  rcases hword with rfl | ⟨pair, rfl⟩
  · exact orientation.baseWord_edgePattern hne hedge
  · exact orientation.separatorWord_edgePattern pair hne hedge

theorem representationWord_uniform (orientation : SemiTransitiveOrientation G) :
    orientation.representationWord.IsUniform
      (orientation.representationBlocks.length * 2) := by
  exact Word.IsUniform.flatten orientation.representationBlocks_uniform

theorem representationWord_edgePattern (orientation : SemiTransitiveOrientation G)
    {left right : V} (hne : left ≠ right) (hedge : orientation.rel left right) :
    orientation.representationWord.restrictToPair left right =
      alternatingPairs left right (orientation.representationBlocks.length * 2) := by
  exact restrictToPair_flatten_eq_alternatingPairs
    orientation.representationBlocks left right 2
      (orientation.representationBlocks_edgePattern hne hedge)

theorem representationWord_covers (orientation : SemiTransitiveOrientation G) :
    orientation.representationWord.Covers := by
  intro vertex
  apply List.count_pos_iff.mp
  rw [orientation.representationWord_uniform vertex]
  simp [representationBlocks]

theorem representationWord_lettersAlternate (orientation : SemiTransitiveOrientation G)
    {left right : V} (hne : left ≠ right) (hedge : orientation.rel left right) :
    LettersAlternate orientation.representationWord left right := by
  refine ⟨hne, ?_⟩
  rw [orientation.representationWord_edgePattern hne hedge]
  exact isAlternating_alternatingPairs hne _

theorem representationWord_not_lettersAlternate
    (orientation : SemiTransitiveOrientation G)
    {left right : V} (hne : left ≠ right) (hnonedge : ¬G.Adj left right) :
    ¬LettersAlternate orientation.representationWord left right := by
  let pair : DistinctNonedge G := ⟨(left, right), hne, hnonedge⟩
  intro halternates
  have hmem : orientation.separatorWord pair ∈ orientation.representationBlocks :=
    orientation.separatorWord_mem_representationBlocks pair
  rcases List.mem_iff_append.mp hmem with ⟨before, after, hblocks⟩
  have hwhole : LettersAlternate
      (before.flatten ++ orientation.separatorWord pair ++ after.flatten)
      left right := by
    simpa [representationWord, hblocks, List.flatten_append, List.append_assoc] using
      halternates
  exact orientation.separatorWord_separates pair hwhole.middle

theorem representationWord_underlying (orientation : SemiTransitiveOrientation G) :
    alternationGraph orientation.representationWord = G := by
  ext left right
  rw [alternationGraph_adj]
  constructor
  · intro halternates
    by_contra hnonedge
    exact orientation.representationWord_not_lettersAlternate halternates.1 hnonedge
      halternates
  · intro hadj
    rw [← orientation.underlying, SimpleGraph.fromRel_adj] at hadj
    rcases hadj with ⟨hne, hedge | hedge⟩
    · exact orientation.representationWord_lettersAlternate hne hedge
    · exact (lettersAlternate_comm orientation.representationWord left right).mpr
        (orientation.representationWord_lettersAlternate hne.symm hedge)

/-- The finite converse construction as a uniform word representation. -/
noncomputable def toUniformWordRepresentation
    (orientation : SemiTransitiveOrientation G) : UniformWordRepresentation G :=
  { representation :=
      { word := orientation.representationWord
        covers := orientation.representationWord_covers
        underlying := orientation.representationWord_underlying }
    multiplicity := orientation.representationBlocks.length * 2
    multiplicity_pos := by simp [representationBlocks]
    uniform := orientation.representationWord_uniform }

end SemiTransitiveOrientation

/-- Every finite semi-transitively orientable graph is uniformly word-representable. -/
theorem IsSemiTransitivelyOrientable.isUniformlyWordRepresentable
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : IsSemiTransitivelyOrientable G) : IsUniformlyWordRepresentable G := by
  rcases hG with ⟨orientation⟩
  exact ⟨orientation.toUniformWordRepresentation⟩

/-- Finite word-representable graphs are exactly the semi-transitively orientable graphs. -/
theorem isWordRepresentable_iff_isSemiTransitivelyOrientable
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    IsWordRepresentable G ↔ IsSemiTransitivelyOrientable G := by
  constructor
  · exact IsWordRepresentable.isSemiTransitivelyOrientable
  · intro hG
    rcases hG.isUniformlyWordRepresentable with ⟨uniformRep⟩
    exact ⟨uniformRep.representation⟩

end Lax458700Proofs
