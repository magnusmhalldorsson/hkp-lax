import Lax458700Proofs.FiniteConverse
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# The corrected HKP representation-number bound

The preliminary HKP proof used a false vertex-covering lemma.  The corrected
construction partitions the vertices relative to a fixed vertex `v` into five
classes and uses the two-uniform word

`A I T A v O I v B T O B`.

Here each capital letter is a topologically ordered list of the corresponding
class.  This module formalizes that construction before using a set of vertices
that meets every nonedge (in particular, the complement of a clique).
-/

namespace Lax458700Proofs

universe u

variable {V : Type u}

namespace SemiTransitiveOrientation

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A fixed topological order of the original orientation. -/
noncomputable def hkpListing (orientation : SemiTransitiveOrientation G) :
    TopologicalListing orientation.rel :=
  TopologicalListing.ofAcyclic orientation.acyclic

/-- Nonneighbors strictly before `pivot` in reachability order. -/
def hkpA (orientation : SemiTransitiveOrientation G) (pivot vertex : V) : Prop :=
  Relation.TransGen orientation.rel vertex pivot ∧ ¬orientation.rel vertex pivot

/-- In-neighbors of `pivot`. -/
def hkpI (orientation : SemiTransitiveOrientation G) (pivot vertex : V) : Prop :=
  orientation.rel vertex pivot

/-- Vertices incomparable with `pivot` in reachability order. -/
def hkpT (orientation : SemiTransitiveOrientation G) (pivot vertex : V) : Prop :=
  vertex ≠ pivot ∧
    ¬Relation.TransGen orientation.rel vertex pivot ∧
    ¬Relation.TransGen orientation.rel pivot vertex

/-- Out-neighbors of `pivot`. -/
def hkpO (orientation : SemiTransitiveOrientation G) (pivot vertex : V) : Prop :=
  orientation.rel pivot vertex

/-- Nonneighbors strictly after `pivot` in reachability order. -/
def hkpB (orientation : SemiTransitiveOrientation G) (pivot vertex : V) : Prop :=
  Relation.TransGen orientation.rel pivot vertex ∧ ¬orientation.rel pivot vertex

/-- The vertices satisfying a class predicate, in the fixed topological order. -/
noncomputable def hkpClassWord (orientation : SemiTransitiveOrientation G)
    (predicate : V → Prop) : Word V := by
  classical
  exact orientation.hkpListing.order.filter fun vertex ↦ decide (predicate vertex)

noncomputable def hkpAWord (orientation : SemiTransitiveOrientation G) (pivot : V) : Word V :=
  orientation.hkpClassWord (orientation.hkpA pivot)

noncomputable def hkpIWord (orientation : SemiTransitiveOrientation G) (pivot : V) : Word V :=
  orientation.hkpClassWord (orientation.hkpI pivot)

noncomputable def hkpTWord (orientation : SemiTransitiveOrientation G) (pivot : V) : Word V :=
  orientation.hkpClassWord (orientation.hkpT pivot)

noncomputable def hkpOWord (orientation : SemiTransitiveOrientation G) (pivot : V) : Word V :=
  orientation.hkpClassWord (orientation.hkpO pivot)

noncomputable def hkpBWord (orientation : SemiTransitiveOrientation G) (pivot : V) : Word V :=
  orientation.hkpClassWord (orientation.hkpB pivot)

/-- Pair restriction distributes over flattening a list of words. -/
@[simp] theorem restrictToPair_flatten_blocks (words : List (Word V))
    (left right : V) :
    Word.restrictToPair words.flatten left right =
      (words.map fun word ↦ Word.restrictToPair word left right).flatten := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      simp only [List.flatten_cons, Word.restrictToPair_append, ih,
        List.map_cons]

/-- A one-letter prefix can be simplified without unfolding the whole restriction. -/
@[simp] theorem restrictToPair_cons (head : V) (tail : Word V)
    (left right : V) :
    Word.restrictToPair (head :: tail) left right =
      (if head = left ∨ head = right then [head] else []) ++
        Word.restrictToPair tail left right := by
  by_cases hpair : head = left ∨ head = right
  · simp [Word.restrictToPair, hpair]
  · simp [Word.restrictToPair, hpair]

/-- The twelve blocks in the corrected HKP construction. -/
noncomputable def hkpVertexBlocks (orientation : SemiTransitiveOrientation G)
    (pivot : V) : List (Word V) :=
  [orientation.hkpAWord pivot,
   orientation.hkpIWord pivot,
   orientation.hkpTWord pivot,
   orientation.hkpAWord pivot,
   [pivot],
   orientation.hkpOWord pivot,
   orientation.hkpIWord pivot,
   [pivot],
   orientation.hkpBWord pivot,
   orientation.hkpTWord pivot,
   orientation.hkpOWord pivot,
   orientation.hkpBWord pivot]

/-- The corrected HKP two-uniform block associated with one vertex. -/
noncomputable def hkpVertexWord (orientation : SemiTransitiveOrientation G)
    (pivot : V) : Word V :=
  (orientation.hkpVertexBlocks pivot).flatten

theorem hkpClassWord_count_eq_one (orientation : SemiTransitiveOrientation G)
    (predicate : V → Prop) (vertex : V) (hpredicate : predicate vertex) :
    (orientation.hkpClassWord predicate).count vertex = 1 := by
  classical
  unfold hkpClassWord
  rw [List.count_filter (by simp [hpredicate])]
  exact List.count_eq_one_of_mem orientation.hkpListing.nodup
    (orientation.hkpListing.complete vertex)

theorem hkpClassWord_count_eq_zero (orientation : SemiTransitiveOrientation G)
    (predicate : V → Prop) (vertex : V) (hpredicate : ¬predicate vertex) :
    (orientation.hkpClassWord predicate).count vertex = 0 := by
  classical
  apply List.count_eq_zero.mpr
  simp [hkpClassWord, hpredicate]

theorem hkpListing_pairwise_idx (orientation : SemiTransitiveOrientation G) :
    orientation.hkpListing.order.Pairwise fun left right ↦
      orientation.hkpListing.order.idxOf left <
        orientation.hkpListing.order.idxOf right := by
  rw [List.pairwise_iff_get]
  intro i j hij
  rw [List.get_idxOf orientation.hkpListing.nodup,
    List.get_idxOf orientation.hkpListing.nodup]
  exact hij

theorem hkpClassWord_nodup (orientation : SemiTransitiveOrientation G)
    (predicate : V → Prop) :
    (orientation.hkpClassWord predicate).Nodup := by
  classical
  exact orientation.hkpListing.nodup.filter _

@[simp] theorem hkpClassWord_restrict_none (orientation : SemiTransitiveOrientation G)
    (predicate : V → Prop) {left right : V}
    (hleft : ¬predicate left) (hright : ¬predicate right) :
    (orientation.hkpClassWord predicate).restrictToPair left right = [] := by
  classical
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro vertex hvertex
  simp [Word.restrictToPair, hkpClassWord] at hvertex
  rcases hvertex with ⟨_, hpair, hpredicate⟩
  rcases hpair with rfl | rfl
  · exact hleft hpredicate
  · exact hright hpredicate

@[simp] theorem hkpClassWord_restrict_left (orientation : SemiTransitiveOrientation G)
    (predicate : V → Prop) {left right : V}
    (hleft : predicate left) (hright : ¬predicate right) :
    (orientation.hkpClassWord predicate).restrictToPair left right = [left] := by
  classical
  apply List.perm_singleton.mp
  apply (List.perm_ext_iff_of_nodup
    ((orientation.hkpClassWord_nodup predicate).filter _)
    (by simp)).mpr
  intro vertex
  simp [Word.restrictToPair, hkpClassWord, hleft, hright,
    orientation.hkpListing.complete]
  aesop

@[simp] theorem hkpClassWord_restrict_right (orientation : SemiTransitiveOrientation G)
    (predicate : V → Prop) {left right : V}
    (hleft : ¬predicate left) (hright : predicate right) :
    (orientation.hkpClassWord predicate).restrictToPair left right = [right] := by
  calc
    (orientation.hkpClassWord predicate).restrictToPair left right =
        (orientation.hkpClassWord predicate).restrictToPair right left :=
      (Word.restrictToPair_comm _ right left).symm
    _ = [right] := orientation.hkpClassWord_restrict_left predicate hright hleft

@[simp] theorem hkpClassWord_restrict_both (orientation : SemiTransitiveOrientation G)
    (predicate : V → Prop) {left right : V}
    (hleft : predicate left) (hright : predicate right)
    (hedge : orientation.rel left right) :
    (orientation.hkpClassWord predicate).restrictToPair left right = [left, right] := by
  classical
  have hne : left ≠ right := fun heq ↦ by
    subst right
    exact orientation.irrefl left hedge
  have hperm : List.Perm
      ((orientation.hkpClassWord predicate).restrictToPair left right)
      [left, right] := by
    apply (List.perm_ext_iff_of_nodup
      ((orientation.hkpClassWord_nodup predicate).filter _)
      (by simp [hne])).mpr
    intro vertex
    simp [Word.restrictToPair, hkpClassWord, hleft, hright,
      orientation.hkpListing.complete]
    aesop
  rcases List.perm_pair.mp hperm with hforward | hreverse
  · exact hforward
  · have hpairwise :
        ((orientation.hkpClassWord predicate).restrictToPair left right).Pairwise
          (fun first second ↦
            orientation.hkpListing.order.idxOf first <
              orientation.hkpListing.order.idxOf second) := by
      exact (orientation.hkpListing_pairwise_idx.filter _).filter _
    rw [hreverse] at hpairwise
    have hbackward : orientation.hkpListing.order.idxOf right <
        orientation.hkpListing.order.idxOf left := by simpa using hpairwise
    exact (Nat.not_lt_of_ge (orientation.hkpListing.respects hedge).le hbackward).elim

/-- The five HKP classes partition all vertices other than the pivot. -/
theorem hkp_class_cases (orientation : SemiTransitiveOrientation G)
    (pivot vertex : V) :
    vertex = pivot ∨
      orientation.hkpA pivot vertex ∨
      orientation.hkpI pivot vertex ∨
      orientation.hkpT pivot vertex ∨
      orientation.hkpO pivot vertex ∨
      orientation.hkpB pivot vertex := by
  by_cases heq : vertex = pivot
  · exact Or.inl heq
  · right
    by_cases hbefore : Relation.TransGen orientation.rel vertex pivot
    · by_cases hedge : orientation.rel vertex pivot
      · exact Or.inr (Or.inl hedge)
      · exact Or.inl ⟨hbefore, hedge⟩
    · by_cases hafter : Relation.TransGen orientation.rel pivot vertex
      · by_cases hedge : orientation.rel pivot vertex
        · exact Or.inr (Or.inr (Or.inr (Or.inl hedge)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hafter, hedge⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨heq, hbefore, hafter⟩))

/-- The possible HKP-class positions of a directed edge. -/
inductive HKPEdgeCase (orientation : SemiTransitiveOrientation G) (pivot left right : V) : Prop
  | aa : orientation.hkpA pivot left → orientation.hkpA pivot right →
      HKPEdgeCase orientation pivot left right
  | ai : orientation.hkpA pivot left → orientation.hkpI pivot right →
      HKPEdgeCase orientation pivot left right
  | at : orientation.hkpA pivot left → orientation.hkpT pivot right →
      HKPEdgeCase orientation pivot left right
  | ii : orientation.hkpI pivot left → orientation.hkpI pivot right →
      HKPEdgeCase orientation pivot left right
  | it : orientation.hkpI pivot left → orientation.hkpT pivot right →
      HKPEdgeCase orientation pivot left right
  | io : orientation.hkpI pivot left → orientation.hkpO pivot right →
      HKPEdgeCase orientation pivot left right
  | iv : orientation.hkpI pivot left → right = pivot →
      HKPEdgeCase orientation pivot left right
  | tt : orientation.hkpT pivot left → orientation.hkpT pivot right →
      HKPEdgeCase orientation pivot left right
  | to : orientation.hkpT pivot left → orientation.hkpO pivot right →
      HKPEdgeCase orientation pivot left right
  | tb : orientation.hkpT pivot left → orientation.hkpB pivot right →
      HKPEdgeCase orientation pivot left right
  | vo : left = pivot → orientation.hkpO pivot right →
      HKPEdgeCase orientation pivot left right
  | oo : orientation.hkpO pivot left → orientation.hkpO pivot right →
      HKPEdgeCase orientation pivot left right
  | ob : orientation.hkpO pivot left → orientation.hkpB pivot right →
      HKPEdgeCase orientation pivot left right
  | bb : orientation.hkpB pivot left → orientation.hkpB pivot right →
      HKPEdgeCase orientation pivot left right

theorem hkp_no_edge_A_to_after (orientation : SemiTransitiveOrientation G)
    {pivot left right : V} (hA : orientation.hkpA pivot left)
    (hafter : Relation.TransGen orientation.rel pivot right) :
    ¬orientation.rel left right := by
  intro hedge
  have hforced : orientation.rel left pivot :=
    orientation.edge_of_reachable_interval
      Relation.ReflTransGen.refl hA.1 hafter.to_reflTransGen hedge
  exact hA.2 hforced

theorem hkp_no_edge_I_to_A (orientation : SemiTransitiveOrientation G)
    {pivot left right : V} (hI : orientation.hkpI pivot left)
    (hA : orientation.hkpA pivot right) :
    ¬orientation.rel left right := by
  intro hedge
  have hforced : orientation.rel right pivot :=
    orientation.edge_of_reachable_interval
      (Relation.ReflTransGen.single hedge) hA.1 Relation.ReflTransGen.refl hI
  exact hA.2 hforced

theorem hkp_no_edge_I_to_B (orientation : SemiTransitiveOrientation G)
    {pivot left right : V} (hI : orientation.hkpI pivot left)
    (hB : orientation.hkpB pivot right) :
    ¬orientation.rel left right := by
  intro hedge
  have hforced : orientation.rel pivot right :=
    orientation.edge_of_reachable_interval
      (Relation.ReflTransGen.single hI) hB.1 Relation.ReflTransGen.refl hedge
  exact hB.2 hforced

theorem hkp_no_edge_B_to_O (orientation : SemiTransitiveOrientation G)
    {pivot left right : V} (hB : orientation.hkpB pivot left)
    (hO : orientation.hkpO pivot right) :
    ¬orientation.rel left right := by
  intro hedge
  have hforced : orientation.rel pivot left :=
    orientation.edge_of_reachable_interval
      Relation.ReflTransGen.refl hB.1
        (Relation.ReflTransGen.single hedge) hO
  exact hB.2 hforced

theorem hkpA_other_false (orientation : SemiTransitiveOrientation G)
    {pivot vertex : V} (hA : orientation.hkpA pivot vertex) :
    ¬orientation.hkpI pivot vertex ∧
    ¬orientation.hkpT pivot vertex ∧
    ¬orientation.hkpO pivot vertex ∧
    ¬orientation.hkpB pivot vertex ∧ pivot ≠ vertex := by
  have hnback : ¬Relation.TransGen orientation.rel pivot vertex := fun path ↦
    orientation.acyclic vertex (hA.1.trans path)
  exact ⟨hA.2, (fun h ↦ h.2.1 hA.1),
    (fun h ↦ hnback (.single h)), (fun h ↦ hnback h.1),
    fun heq ↦ by subst vertex; exact orientation.acyclic pivot hA.1⟩

theorem hkpI_other_false (orientation : SemiTransitiveOrientation G)
    {pivot vertex : V} (hI : orientation.hkpI pivot vertex) :
    ¬orientation.hkpA pivot vertex ∧
    ¬orientation.hkpT pivot vertex ∧
    ¬orientation.hkpO pivot vertex ∧
    ¬orientation.hkpB pivot vertex ∧ pivot ≠ vertex := by
  have hbefore : Relation.TransGen orientation.rel vertex pivot := .single hI
  have hnback : ¬Relation.TransGen orientation.rel pivot vertex := fun path ↦
    orientation.acyclic vertex (hbefore.trans path)
  exact ⟨(fun h ↦ h.2 hI), (fun h ↦ h.2.1 hbefore),
    (fun h ↦ hnback (.single h)), (fun h ↦ hnback h.1),
    fun heq ↦ by subst vertex; exact orientation.irrefl pivot hI⟩

theorem hkpT_other_false (orientation : SemiTransitiveOrientation G)
    {pivot vertex : V} (hT : orientation.hkpT pivot vertex) :
    ¬orientation.hkpA pivot vertex ∧
    ¬orientation.hkpI pivot vertex ∧
    ¬orientation.hkpO pivot vertex ∧
    ¬orientation.hkpB pivot vertex ∧ pivot ≠ vertex :=
  ⟨(fun h ↦ hT.2.1 h.1), (fun h ↦ hT.2.1 (.single h)),
    (fun h ↦ hT.2.2 (.single h)), (fun h ↦ hT.2.2 h.1), hT.1.symm⟩

theorem hkpO_other_false (orientation : SemiTransitiveOrientation G)
    {pivot vertex : V} (hO : orientation.hkpO pivot vertex) :
    ¬orientation.hkpA pivot vertex ∧
    ¬orientation.hkpI pivot vertex ∧
    ¬orientation.hkpT pivot vertex ∧
    ¬orientation.hkpB pivot vertex ∧ pivot ≠ vertex := by
  have hafter : Relation.TransGen orientation.rel pivot vertex := .single hO
  have hnbefore : ¬Relation.TransGen orientation.rel vertex pivot := fun path ↦
    orientation.acyclic pivot (hafter.trans path)
  exact ⟨(fun h ↦ hnbefore h.1), (fun h ↦ hnbefore (.single h)),
    (fun h ↦ h.2.2 hafter), (fun h ↦ h.2 hO),
    fun heq ↦ by subst vertex; exact orientation.irrefl pivot hO⟩

theorem hkpB_other_false (orientation : SemiTransitiveOrientation G)
    {pivot vertex : V} (hB : orientation.hkpB pivot vertex) :
    ¬orientation.hkpA pivot vertex ∧
    ¬orientation.hkpI pivot vertex ∧
    ¬orientation.hkpT pivot vertex ∧
    ¬orientation.hkpO pivot vertex ∧ pivot ≠ vertex := by
  have hnbefore : ¬Relation.TransGen orientation.rel vertex pivot := fun path ↦
    orientation.acyclic pivot (hB.1.trans path)
  exact ⟨(fun h ↦ hnbefore h.1), (fun h ↦ hnbefore (.single h)),
    (fun h ↦ h.2.2 hB.1), hB.2,
    fun heq ↦ by subst vertex; exact orientation.acyclic pivot hB.1⟩

theorem hkpPivot_false (orientation : SemiTransitiveOrientation G) (pivot : V) :
    ¬orientation.hkpA pivot pivot ∧
    ¬orientation.hkpI pivot pivot ∧
    ¬orientation.hkpT pivot pivot ∧
    ¬orientation.hkpO pivot pivot ∧
    ¬orientation.hkpB pivot pivot := by
  exact ⟨(fun h ↦ orientation.acyclic pivot h.1), orientation.irrefl pivot,
    (fun h ↦ h.1 rfl), orientation.irrefl pivot,
    fun h ↦ orientation.acyclic pivot h.1⟩

/-- Every directed edge lies in one of the three cliques represented by the corrected
HKP word: `A∪I∪T`, `I∪{v}∪O`, or `T∪O∪B`. -/
theorem hkp_edge_case (orientation : SemiTransitiveOrientation G)
    (pivot : V) {left right : V} (hedge : orientation.rel left right) :
    HKPEdgeCase orientation pivot left right := by
  rcases orientation.hkp_class_cases pivot left with
    rfl | hAl | hIl | hTl | hOl | hBl
  · exact .vo rfl hedge
  · rcases orientation.hkp_class_cases pivot right with
      rfl | hAr | hIr | hTr | hOr | hBr
    · exact (hAl.2 hedge).elim
    · exact .aa hAl hAr
    · exact .ai hAl hIr
    · exact .at hAl hTr
    · exact (orientation.hkp_no_edge_A_to_after hAl (.single hOr) hedge).elim
    · exact (orientation.hkp_no_edge_A_to_after hAl hBr.1 hedge).elim
  · rcases orientation.hkp_class_cases pivot right with
      rfl | hAr | hIr | hTr | hOr | hBr
    · exact .iv hIl rfl
    · exact (orientation.hkp_no_edge_I_to_A hIl hAr hedge).elim
    · exact .ii hIl hIr
    · exact .it hIl hTr
    · exact .io hIl hOr
    · exact (orientation.hkp_no_edge_I_to_B hIl hBr hedge).elim
  · rcases orientation.hkp_class_cases pivot right with
      rfl | hAr | hIr | hTr | hOr | hBr
    · exact (hTl.2.1 (Relation.TransGen.single hedge)).elim
    · exact (hTl.2.1 ((Relation.TransGen.single hedge).trans hAr.1)).elim
    · exact (hTl.2.1 ((Relation.TransGen.single hedge).tail hIr)).elim
    · exact .tt hTl hTr
    · exact .to hTl hOr
    · exact .tb hTl hBr
  · rcases orientation.hkp_class_cases pivot right with
      rfl | hAr | hIr | hTr | hOr | hBr
    · exact (orientation.asymm hOl hedge).elim
    · exact (orientation.acyclic pivot
        ((Relation.TransGen.single hOl).tail hedge |>.trans hAr.1)).elim
    · exact (orientation.acyclic pivot
        ((Relation.TransGen.single hOl).tail hedge |>.tail hIr)).elim
    · exact (hTr.2.2 ((Relation.TransGen.single hOl).tail hedge)).elim
    · exact .oo hOl hOr
    · exact .ob hOl hBr
  · rcases orientation.hkp_class_cases pivot right with
      rfl | hAr | hIr | hTr | hOr | hBr
    · exact (orientation.acyclic right (hBl.1.tail hedge)).elim
    · exact (orientation.acyclic pivot ((hBl.1.tail hedge).trans hAr.1)).elim
    · exact (orientation.acyclic pivot ((hBl.1.tail hedge).tail hIr)).elim
    · exact (hTr.2.2 (hBl.1.tail hedge)).elim
    · exact (orientation.hkp_no_edge_B_to_O hBl hOr hedge).elim
    · exact .bb hBl hBr

/-- Every original directed edge has the exact `left right left right` pattern in a
corrected HKP vertex block. -/
theorem hkpVertexWord_edgePattern (orientation : SemiTransitiveOrientation G)
    (pivot : V) {left right : V} (hedge : orientation.rel left right) :
    (orientation.hkpVertexWord pivot).restrictToPair left right =
      alternatingPairs left right 2 := by
  have hne : left ≠ right := fun heq ↦ by
    subst right
    exact orientation.irrefl left hedge
  rcases orientation.hkp_edge_case pivot hedge with
    ⟨hAl, hAr⟩ | ⟨hAl, hIr⟩ | ⟨hAl, hTr⟩ |
    ⟨hIl, hIr⟩ | ⟨hIl, hTr⟩ | ⟨hIl, hOr⟩ | ⟨hIl, hright⟩ |
    ⟨hTl, hTr⟩ | ⟨hTl, hOr⟩ | ⟨hTl, hBr⟩ | ⟨hleft, hOr⟩ |
    ⟨hOl, hOr⟩ | ⟨hOl, hBr⟩ | ⟨hBl, hBr⟩
  ·
    rcases orientation.hkpA_other_false hAl with ⟨hIl, hTl, hOl, hBl, hpl⟩
    rcases orientation.hkpA_other_false hAr with ⟨hIr, hTr, hOr, hBr, hpr⟩
    simp [hkpVertexWord, hkpVertexBlocks, hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      hAl, hAr, hIl, hIr, hTl, hTr, hOl, hOr, hBl, hBr, hpl, hpr,
      hedge, alternatingPairs]
  ·
    rcases orientation.hkpA_other_false hAl with ⟨hIl, hTl, hOl, hBl, hpl⟩
    rcases orientation.hkpI_other_false hIr with ⟨hAr, hTr, hOr, hBr, hpr⟩
    simp [hkpVertexWord, hkpVertexBlocks, hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      hAl, hAr, hIl, hIr, hTl, hTr, hOl, hOr, hBl, hBr, hpl, hpr,
      hedge, alternatingPairs]
  ·
    rcases orientation.hkpA_other_false hAl with ⟨hIl, hTl, hOl, hBl, hpl⟩
    rcases orientation.hkpT_other_false hTr with ⟨hAr, hIr, hOr, hBr, hpr⟩
    simp [hkpVertexWord, hkpVertexBlocks, hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      hAl, hAr, hIl, hIr, hTl, hTr, hOl, hOr, hBl, hBr, hpl, hpr,
      hedge, alternatingPairs]
  ·
    rcases orientation.hkpI_other_false hIl with ⟨hAl, hTl, hOl, hBl, hpl⟩
    rcases orientation.hkpI_other_false hIr with ⟨hAr, hTr, hOr, hBr, hpr⟩
    simp [hkpVertexWord, hkpVertexBlocks, hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      hAl, hAr, hIl, hIr, hTl, hTr, hOl, hOr, hBl, hBr, hpl, hpr,
      hedge, alternatingPairs]
  ·
    rcases orientation.hkpI_other_false hIl with ⟨hAl, hTl, hOl, hBl, hpl⟩
    rcases orientation.hkpT_other_false hTr with ⟨hAr, hIr, hOr, hBr, hpr⟩
    simp [hkpVertexWord, hkpVertexBlocks, hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      hAl, hAr, hIl, hIr, hTl, hTr, hOl, hOr, hBl, hBr, hpl, hpr,
      hedge, alternatingPairs]
  ·
    rcases orientation.hkpI_other_false hIl with ⟨hAl, hTl, hOl, hBl, hpl⟩
    rcases orientation.hkpO_other_false hOr with ⟨hAr, hIr, hTr, hBr, hpr⟩
    simp [hkpVertexWord, hkpVertexBlocks, hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      hAl, hAr, hIl, hIr, hTl, hTr, hOl, hOr, hBl, hBr, hpl, hpr,
      hedge, alternatingPairs]
  · subst right
    rcases orientation.hkpI_other_false hIl with ⟨hAl, hTl, hOl, hBl, hpl⟩
    rcases orientation.hkpPivot_false pivot with ⟨hAp, hIp, hTp, hOp, hBp⟩
    simp [hkpVertexWord, hkpVertexBlocks, hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      hAl, hIl, hTl, hOl, hBl, hAp, hIp, hTp, hOp, hBp, hpl, hedge, orientation.irrefl,
      orientation.acyclic, alternatingPairs]
  ·
    rcases orientation.hkpT_other_false hTl with ⟨hAl, hIl, hOl, hBl, hpl⟩
    rcases orientation.hkpT_other_false hTr with ⟨hAr, hIr, hOr, hBr, hpr⟩
    simp [hkpVertexWord, hkpVertexBlocks, hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      hAl, hAr, hIl, hIr, hTl, hTr, hOl, hOr, hBl, hBr, hpl, hpr,
      hedge, alternatingPairs]
  ·
    rcases orientation.hkpT_other_false hTl with ⟨hAl, hIl, hOl, hBl, hpl⟩
    rcases orientation.hkpO_other_false hOr with ⟨hAr, hIr, hTr, hBr, hpr⟩
    simp [hkpVertexWord, hkpVertexBlocks, hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      hAl, hAr, hIl, hIr, hTl, hTr, hOl, hOr, hBl, hBr, hpl, hpr,
      hedge, alternatingPairs]
  ·
    rcases orientation.hkpT_other_false hTl with ⟨hAl, hIl, hOl, hBl, hpl⟩
    rcases orientation.hkpB_other_false hBr with ⟨hAr, hIr, hTr, hOr, hpr⟩
    simp [hkpVertexWord, hkpVertexBlocks, hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      hAl, hAr, hIl, hIr, hTl, hTr, hOl, hOr, hBl, hBr, hpl, hpr,
      hedge, alternatingPairs]
  · subst left
    rcases orientation.hkpO_other_false hOr with ⟨hAr, hIr, hTr, hBr, hpr⟩
    rcases orientation.hkpPivot_false pivot with ⟨hAp, hIp, hTp, hOp, hBp⟩
    simp [hkpVertexWord, hkpVertexBlocks, hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      hAr, hIr, hTr, hOr, hBr, hAp, hIp, hTp, hOp, hBp, hpr, hedge, orientation.irrefl,
      orientation.acyclic, alternatingPairs]
  ·
    rcases orientation.hkpO_other_false hOl with ⟨hAl, hIl, hTl, hBl, hpl⟩
    rcases orientation.hkpO_other_false hOr with ⟨hAr, hIr, hTr, hBr, hpr⟩
    simp [hkpVertexWord, hkpVertexBlocks, hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      hAl, hAr, hIl, hIr, hTl, hTr, hOl, hOr, hBl, hBr, hpl, hpr,
      hedge, alternatingPairs]
  ·
    rcases orientation.hkpO_other_false hOl with ⟨hAl, hIl, hTl, hBl, hpl⟩
    rcases orientation.hkpB_other_false hBr with ⟨hAr, hIr, hTr, hOr, hpr⟩
    simp [hkpVertexWord, hkpVertexBlocks, hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      hAl, hAr, hIl, hIr, hTl, hTr, hOl, hOr, hBl, hBr, hpl, hpr,
      hedge, alternatingPairs]
  ·
    rcases orientation.hkpB_other_false hBl with ⟨hAl, hIl, hTl, hOl, hpl⟩
    rcases orientation.hkpB_other_false hBr with ⟨hAr, hIr, hTr, hOr, hpr⟩
    simp [hkpVertexWord, hkpVertexBlocks, hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      hAl, hAr, hIl, hIr, hTl, hTr, hOl, hOr, hBl, hBr, hpl, hpr,
      hedge, alternatingPairs]

/-- Every letter occurs exactly twice in the corrected vertex block. -/
theorem hkpVertexWord_uniform (orientation : SemiTransitiveOrientation G)
    (pivot : V) :
    (orientation.hkpVertexWord pivot).IsUniform 2 := by
  classical
  intro vertex
  rcases orientation.hkp_class_cases pivot vertex with
    rfl | hA | hI | hT | hO | hB
  · have hA' : ¬orientation.hkpA vertex vertex := by
      simp [hkpA, orientation.acyclic]
    have hI' : ¬orientation.hkpI vertex vertex := orientation.irrefl vertex
    have hT' : ¬orientation.hkpT vertex vertex := by simp [hkpT]
    have hO' : ¬orientation.hkpO vertex vertex := orientation.irrefl vertex
    have hB' : ¬orientation.hkpB vertex vertex := by
      simp [hkpB, orientation.acyclic]
    simp only [hkpVertexWord, hkpVertexBlocks, List.flatten_cons, List.flatten_nil, List.count_append, List.count_cons, List.count_nil,
      hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      orientation.hkpClassWord_count_eq_zero _ _ hA',
      orientation.hkpClassWord_count_eq_zero _ _ hI',
      orientation.hkpClassWord_count_eq_zero _ _ hT',
      orientation.hkpClassWord_count_eq_zero _ _ hO',
      orientation.hkpClassWord_count_eq_zero _ _ hB']
    simp
  · have hnback : ¬Relation.TransGen orientation.rel pivot vertex := fun path ↦
      orientation.acyclic vertex (hA.1.trans path)
    have hnreverse : ¬orientation.rel pivot vertex := fun hedge ↦
      hnback (.single hedge)
    have hI' : ¬orientation.hkpI pivot vertex := hA.2
    have hT' : ¬orientation.hkpT pivot vertex := fun h ↦ h.2.1 hA.1
    have hO' : ¬orientation.hkpO pivot vertex := hnreverse
    have hB' : ¬orientation.hkpB pivot vertex := fun h ↦ hnback h.1
    have hne : pivot ≠ vertex := by
      intro heq; subst vertex; exact orientation.acyclic pivot hA.1
    simp only [hkpVertexWord, hkpVertexBlocks, List.flatten_cons, List.flatten_nil, List.count_append, List.count_cons, List.count_nil,
      hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      orientation.hkpClassWord_count_eq_one _ _ hA,
      orientation.hkpClassWord_count_eq_zero _ _ hI',
      orientation.hkpClassWord_count_eq_zero _ _ hT',
      orientation.hkpClassWord_count_eq_zero _ _ hO',
      orientation.hkpClassWord_count_eq_zero _ _ hB']
    simp [hne]

  · have hbefore : Relation.TransGen orientation.rel vertex pivot := .single hI
    have hnback : ¬Relation.TransGen orientation.rel pivot vertex := fun path ↦
      orientation.acyclic vertex (hbefore.trans path)
    have hnreverse : ¬orientation.rel pivot vertex := fun hedge ↦
      hnback (.single hedge)
    have hA' : ¬orientation.hkpA pivot vertex := fun h ↦ h.2 hI
    have hT' : ¬orientation.hkpT pivot vertex := fun h ↦ h.2.1 hbefore
    have hO' : ¬orientation.hkpO pivot vertex := hnreverse
    have hB' : ¬orientation.hkpB pivot vertex := fun h ↦ hnback h.1
    have hne : pivot ≠ vertex := by
      intro heq; subst vertex; exact orientation.irrefl pivot hI
    simp only [hkpVertexWord, hkpVertexBlocks, List.flatten_cons, List.flatten_nil, List.count_append, List.count_cons, List.count_nil,
      hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      orientation.hkpClassWord_count_eq_zero _ _ hA',
      orientation.hkpClassWord_count_eq_one _ _ hI,
      orientation.hkpClassWord_count_eq_zero _ _ hT',
      orientation.hkpClassWord_count_eq_zero _ _ hO',
      orientation.hkpClassWord_count_eq_zero _ _ hB']
    simp [hne]
  · have hI' : ¬orientation.hkpI pivot vertex := fun hedge ↦ hT.2.1 (.single hedge)
    have hO' : ¬orientation.hkpO pivot vertex := fun hedge ↦ hT.2.2 (.single hedge)
    have hA' : ¬orientation.hkpA pivot vertex := fun h ↦ hT.2.1 h.1
    have hB' : ¬orientation.hkpB pivot vertex := fun h ↦ hT.2.2 h.1
    have hne : pivot ≠ vertex := hT.1.symm
    simp only [hkpVertexWord, hkpVertexBlocks, List.flatten_cons, List.flatten_nil, List.count_append, List.count_cons, List.count_nil,
      hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      orientation.hkpClassWord_count_eq_zero _ _ hA',
      orientation.hkpClassWord_count_eq_zero _ _ hI',
      orientation.hkpClassWord_count_eq_one _ _ hT,
      orientation.hkpClassWord_count_eq_zero _ _ hO',
      orientation.hkpClassWord_count_eq_zero _ _ hB']
    simp [hne]
  · have hafter : Relation.TransGen orientation.rel pivot vertex := .single hO
    have hnbefore : ¬Relation.TransGen orientation.rel vertex pivot := fun path ↦
      orientation.acyclic pivot (hafter.trans path)
    have hnreverse : ¬orientation.rel vertex pivot := fun hedge ↦
      hnbefore (.single hedge)
    have hA' : ¬orientation.hkpA pivot vertex := fun h ↦ hnbefore h.1
    have hI' : ¬orientation.hkpI pivot vertex := hnreverse
    have hT' : ¬orientation.hkpT pivot vertex := fun h ↦ h.2.2 hafter
    have hB' : ¬orientation.hkpB pivot vertex := fun h ↦ h.2 hO
    have hne : pivot ≠ vertex := by
      intro heq; subst vertex; exact orientation.irrefl pivot hO
    simp only [hkpVertexWord, hkpVertexBlocks, List.flatten_cons, List.flatten_nil, List.count_append, List.count_cons, List.count_nil,
      hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      orientation.hkpClassWord_count_eq_zero _ _ hA',
      orientation.hkpClassWord_count_eq_zero _ _ hI',
      orientation.hkpClassWord_count_eq_zero _ _ hT',
      orientation.hkpClassWord_count_eq_one _ _ hO,
      orientation.hkpClassWord_count_eq_zero _ _ hB']
    simp [hne]
  · have hnbefore : ¬Relation.TransGen orientation.rel vertex pivot := fun path ↦
      orientation.acyclic pivot (hB.1.trans path)
    have hnreverse : ¬orientation.rel vertex pivot := fun hedge ↦
      hnbefore (.single hedge)
    have hA' : ¬orientation.hkpA pivot vertex := fun h ↦ hnbefore h.1
    have hI' : ¬orientation.hkpI pivot vertex := hnreverse
    have hT' : ¬orientation.hkpT pivot vertex := fun h ↦ h.2.2 hB.1
    have hO' : ¬orientation.hkpO pivot vertex := hB.2
    have hne : pivot ≠ vertex := by
      intro heq; subst vertex; exact orientation.acyclic pivot hB.1
    simp only [hkpVertexWord, hkpVertexBlocks, List.flatten_cons, List.flatten_nil, List.count_append, List.count_cons, List.count_nil,
      hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      orientation.hkpClassWord_count_eq_zero _ _ hA',
      orientation.hkpClassWord_count_eq_zero _ _ hI',
      orientation.hkpClassWord_count_eq_zero _ _ hT',
      orientation.hkpClassWord_count_eq_zero _ _ hO',
      orientation.hkpClassWord_count_eq_one _ _ hB]
    simp [hne]

theorem hkpVertexWord_covers (orientation : SemiTransitiveOrientation G)
    (pivot : V) :
    (orientation.hkpVertexWord pivot).Covers := by
  intro vertex
  apply List.count_pos_iff.mp
  rw [orientation.hkpVertexWord_uniform pivot vertex]
  decide

theorem hkpVertexWord_lettersAlternate (orientation : SemiTransitiveOrientation G)
    (pivot : V) {left right : V} (hedge : orientation.rel left right) :
    LettersAlternate (orientation.hkpVertexWord pivot) left right := by
  refine ⟨fun heq ↦ by subst right; exact orientation.irrefl left hedge, ?_⟩
  rw [orientation.hkpVertexWord_edgePattern pivot hedge]
  exact isAlternating_alternatingPairs
    (fun heq ↦ by subst right; exact orientation.irrefl left hedge) 2

/-- The corrected vertex block separates every nonedge incident with its pivot. -/
theorem hkpVertexWord_not_lettersAlternate_of_nonedge
    (orientation : SemiTransitiveOrientation G)
    {pivot other : V} (hne : other ≠ pivot) (hnonedge : ¬G.Adj other pivot) :
    ¬LettersAlternate (orientation.hkpVertexWord pivot) other pivot := by
  have hI : ¬orientation.hkpI pivot other := fun hedge ↦
    hnonedge (orientation.rel_implies_adj hedge)
  have hO : ¬orientation.hkpO pivot other := fun hedge ↦
    hnonedge (G.adj_symm (orientation.rel_implies_adj hedge))
  rcases orientation.hkp_class_cases pivot other with
    heq | hA | hI' | hT | hO' | hB
  · exact (hne heq).elim
  · rcases orientation.hkpA_other_false hA with ⟨_, hT', hO', hB', hp⟩
    rcases orientation.hkpPivot_false pivot with ⟨hAp, hIp, hTp, hOp, hBp⟩
    simp [LettersAlternate, IsAlternating, hkpVertexWord, hkpVertexBlocks,
      hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      hA, hI, hT', hO', hB', hAp, hIp, hTp, hOp, hBp, hp, hne]
  · exact (hI hI').elim
  · rcases orientation.hkpT_other_false hT with ⟨hA', _, hO', hB', hp⟩
    rcases orientation.hkpPivot_false pivot with ⟨hAp, hIp, hTp, hOp, hBp⟩
    simp [LettersAlternate, IsAlternating, hkpVertexWord, hkpVertexBlocks,
      hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      hA', hI, hT, hO', hB', hAp, hIp, hTp, hOp, hBp, hp, hne]
  · exact (hO hO').elim
  · rcases orientation.hkpB_other_false hB with ⟨hA', _, hT', hO', hp⟩
    rcases orientation.hkpPivot_false pivot with ⟨hAp, hIp, hTp, hOp, hBp⟩
    simp [LettersAlternate, IsAlternating, hkpVertexWord, hkpVertexBlocks,
      hkpAWord, hkpIWord, hkpTWord, hkpOWord, hkpBWord,
      hA', hI, hT', hO', hB, hAp, hIp, hTp, hOp, hBp, hp, hne]

/-- A vertex set hits every nonedge when every distinct nonadjacent pair has at least
one endpoint in the set.  This is a vertex cover of the complement graph. -/
def HitsEveryNonedge (G : SimpleGraph V) (vertices : Finset V) : Prop :=
  ∀ ⦃left right : V⦄, left ≠ right → ¬G.Adj left right →
    left ∈ vertices ∨ right ∈ vertices

/-- One corrected two-uniform block for every vertex in a nonedge-hitting set. -/
noncomputable def hkpHittingBlocks (orientation : SemiTransitiveOrientation G)
    (vertices : Finset V) : List (Word V) :=
  vertices.toList.map orientation.hkpVertexWord

noncomputable def hkpHittingWord (orientation : SemiTransitiveOrientation G)
    (vertices : Finset V) : Word V :=
  (orientation.hkpHittingBlocks vertices).flatten

theorem hkpVertexWord_mem_hittingBlocks (orientation : SemiTransitiveOrientation G)
    (vertices : Finset V) {vertex : V} (hvertex : vertex ∈ vertices) :
    orientation.hkpVertexWord vertex ∈ orientation.hkpHittingBlocks vertices := by
  classical
  simp only [hkpHittingBlocks, List.mem_map, Finset.mem_toList]
  exact ⟨vertex, hvertex, rfl⟩

theorem hkpHittingBlocks_length (orientation : SemiTransitiveOrientation G)
    (vertices : Finset V) :
    (orientation.hkpHittingBlocks vertices).length = vertices.card := by
  classical
  simp [hkpHittingBlocks]

theorem hkpHittingWord_uniform (orientation : SemiTransitiveOrientation G)
    (vertices : Finset V) :
    (orientation.hkpHittingWord vertices).IsUniform (vertices.card * 2) := by
  rw [hkpHittingWord, ← orientation.hkpHittingBlocks_length vertices]
  exact Word.IsUniform.flatten fun word hword ↦ by
    simp only [hkpHittingBlocks, List.mem_map, Finset.mem_toList] at hword
    rcases hword with ⟨vertex, _, rfl⟩
    exact orientation.hkpVertexWord_uniform vertex

theorem hkpHittingWord_edgePattern (orientation : SemiTransitiveOrientation G)
    (vertices : Finset V) {left right : V} (hedge : orientation.rel left right) :
    (orientation.hkpHittingWord vertices).restrictToPair left right =
      alternatingPairs left right (vertices.card * 2) := by
  rw [hkpHittingWord, ← orientation.hkpHittingBlocks_length vertices]
  exact restrictToPair_flatten_eq_alternatingPairs
    (orientation.hkpHittingBlocks vertices) left right 2 fun word hword ↦ by
      simp only [hkpHittingBlocks, List.mem_map, Finset.mem_toList] at hword
      rcases hword with ⟨vertex, _, rfl⟩
      exact orientation.hkpVertexWord_edgePattern vertex hedge

theorem hkpHittingWord_covers (orientation : SemiTransitiveOrientation G)
    {vertices : Finset V} (hnonempty : vertices.Nonempty) :
    (orientation.hkpHittingWord vertices).Covers := by
  intro vertex
  apply List.count_pos_iff.mp
  rw [orientation.hkpHittingWord_uniform vertices vertex]
  have hcard : 0 < vertices.card := Finset.card_pos.mpr hnonempty
  omega

theorem hkpHittingWord_lettersAlternate (orientation : SemiTransitiveOrientation G)
    (vertices : Finset V) {left right : V} (hedge : orientation.rel left right) :
    LettersAlternate (orientation.hkpHittingWord vertices) left right := by
  have hne : left ≠ right := fun heq ↦ by
    subst right
    exact orientation.irrefl left hedge
  refine ⟨hne, ?_⟩
  rw [orientation.hkpHittingWord_edgePattern vertices hedge]
  exact isAlternating_alternatingPairs hne _

theorem hkpHittingWord_not_lettersAlternate
    (orientation : SemiTransitiveOrientation G)
    {vertices : Finset V} (hhits : HitsEveryNonedge G vertices)
    {left right : V} (hne : left ≠ right) (hnonedge : ¬G.Adj left right) :
    ¬LettersAlternate (orientation.hkpHittingWord vertices) left right := by
  rcases hhits hne hnonedge with hleft | hright
  · have hmem := orientation.hkpVertexWord_mem_hittingBlocks vertices hleft
    rcases List.mem_iff_append.mp hmem with ⟨before, after, hblocks⟩
    intro halternates
    have hwhole : LettersAlternate
        (before.flatten ++ orientation.hkpVertexWord left ++ after.flatten)
        left right := by
      simpa [hkpHittingWord, hblocks, List.flatten_append, List.append_assoc] using
        halternates
    have hmiddle : LettersAlternate (orientation.hkpVertexWord left) right left := by
      apply (lettersAlternate_comm _ left right).mp
      exact hwhole.middle
    exact orientation.hkpVertexWord_not_lettersAlternate_of_nonedge
      hne.symm (fun hadj ↦ hnonedge (G.adj_symm hadj)) hmiddle
  · have hmem := orientation.hkpVertexWord_mem_hittingBlocks vertices hright
    rcases List.mem_iff_append.mp hmem with ⟨before, after, hblocks⟩
    intro halternates
    have hwhole : LettersAlternate
        (before.flatten ++ orientation.hkpVertexWord right ++ after.flatten)
        left right := by
      simpa [hkpHittingWord, hblocks, List.flatten_append, List.append_assoc] using
        halternates
    have hmiddle : LettersAlternate (orientation.hkpVertexWord right) left right := by
      exact hwhole.middle
    exact orientation.hkpVertexWord_not_lettersAlternate_of_nonedge
      hne hnonedge hmiddle

theorem hkpHittingWord_underlying (orientation : SemiTransitiveOrientation G)
    {vertices : Finset V} (hhits : HitsEveryNonedge G vertices) :
    alternationGraph (orientation.hkpHittingWord vertices) = G := by
  ext left right
  rw [alternationGraph_adj]
  constructor
  · intro halternates
    by_contra hnonedge
    exact orientation.hkpHittingWord_not_lettersAlternate hhits
      halternates.1 hnonedge halternates
  · intro hadj
    rw [← orientation.underlying, SimpleGraph.fromRel_adj] at hadj
    rcases hadj with ⟨hne, hedge | hedge⟩
    · exact orientation.hkpHittingWord_lettersAlternate vertices hedge
    · exact (lettersAlternate_comm _ left right).mpr
        (orientation.hkpHittingWord_lettersAlternate vertices hedge)

/-- A nonempty nonedge-hitting set of size `s` gives a `2s`-uniform representation. -/
noncomputable def toUniformWordRepresentationOfHittingSet
    (orientation : SemiTransitiveOrientation G) (vertices : Finset V)
    (hnonempty : vertices.Nonempty) (hhits : HitsEveryNonedge G vertices) :
    UniformWordRepresentation G :=
  { representation :=
      { word := orientation.hkpHittingWord vertices
        covers := orientation.hkpHittingWord_covers hnonempty
        underlying := orientation.hkpHittingWord_underlying hhits }
    multiplicity := vertices.card * 2
    multiplicity_pos := Nat.mul_pos (Finset.card_pos.mpr hnonempty) (by decide)
    uniform := orientation.hkpHittingWord_uniform vertices }

theorem clique_compl_hitsEveryNonedge (orientation : SemiTransitiveOrientation G)
    {clique : Finset V} (hclique : G.IsClique clique) :
    HitsEveryNonedge G cliqueᶜ := by
  intro left right hne hnonedge
  by_cases hleft : left ∈ cliqueᶜ
  · exact Or.inl hleft
  · right
    by_contra hright
    have hleftClique : left ∈ clique := by simpa using hleft
    have hrightClique : right ∈ clique := by simpa using hright
    exact hnonedge (hclique hleftClique hrightClique hne)

theorem clique_compl_nonempty_of_ne_top
    {clique : Finset V} (hclique : G.IsClique clique) (hneTop : G ≠ ⊤) :
    cliqueᶜ.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hfull : clique = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro vertex
    by_contra hvertex
    have hcompl : vertex ∈ cliqueᶜ := by simp [hvertex]
    rw [hempty] at hcompl
    simp at hcompl
  apply hneTop
  rw [← SimpleGraph.isClique_univ]
  simpa [hfull] using hclique

/-- The corrected HKP clique construction.  For a non-complete graph and any clique
`K`, it gives a `2 (|V| - |K|)`-uniform representation. -/
noncomputable def toUniformWordRepresentationOfClique
    (orientation : SemiTransitiveOrientation G) (clique : Finset V)
    (hclique : G.IsClique clique) (hneTop : G ≠ ⊤) :
    UniformWordRepresentation G :=
  orientation.toUniformWordRepresentationOfHittingSet cliqueᶜ
    (clique_compl_nonempty_of_ne_top hclique hneTop)
    (orientation.clique_compl_hitsEveryNonedge hclique)

theorem toUniformWordRepresentationOfClique_multiplicity
    (orientation : SemiTransitiveOrientation G) (clique : Finset V)
    (hclique : G.IsClique clique) (hneTop : G ≠ ⊤) :
    (orientation.toUniformWordRepresentationOfClique clique hclique hneTop).multiplicity =
      (Fintype.card V - clique.card) * 2 := by
  simp [toUniformWordRepresentationOfClique,
    toUniformWordRepresentationOfHittingSet, Finset.card_compl]

end SemiTransitiveOrientation

/-- Corrected HKP bound using a maximum clique.  This is a witness form of the
representation-number bound `2(n - κ)` for finite non-complete graphs. -/
theorem IsSemiTransitivelyOrientable.exists_uniformWordRepresentation_cliqueBound
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : IsSemiTransitivelyOrientable G) (hneTop : G ≠ ⊤) :
    ∃ representation : UniformWordRepresentation G,
      representation.multiplicity =
        2 * (Fintype.card V - G.cliqueNum) := by
  rcases hG with ⟨orientation⟩
  obtain ⟨clique, hclique⟩ := G.exists_isNClique_cliqueNum
  let representation := orientation.toUniformWordRepresentationOfClique
    clique hclique.isClique hneTop
  refine ⟨representation, ?_⟩
  rw [show representation.multiplicity = (Fintype.card V - clique.card) * 2 by
    exact orientation.toUniformWordRepresentationOfClique_multiplicity
      clique hclique.isClique hneTop]
  rw [hclique.card_eq]
  omega

theorem IsWordRepresentable.exists_uniformWordRepresentation_cliqueBound
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : IsWordRepresentable G) (hneTop : G ≠ ⊤) :
    ∃ representation : UniformWordRepresentation G,
      representation.multiplicity =
        2 * (Fintype.card V - G.cliqueNum) :=
  hG.isSemiTransitivelyOrientable.exists_uniformWordRepresentation_cliqueBound hneTop

end Lax458700Proofs
