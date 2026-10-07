import Lax458700Proofs.SemiTransitive
import Lax458700Proofs.Word
import Lax458700Proofs.UniformWordOrientation
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.List
import Mathlib.Data.List.Perm.Basic
import Mathlib.Order.Extension.Linear
import Mathlib.Order.Interval.Finset.Fin

/-!
# String digraphs and topological listings

This module begins the finite converse construction of Halldórsson–Kitaev–Pyatkin (HKP).
The `t`-string digraph contains `t` indexed copies of every vertex. Within one layer it
uses the original orientation; between increasing layers it uses the reverse orientation.
Thus every oriented edge `left → right` forces the chain
`left⁰ < right⁰ < left¹ < right¹ < ...` in every topological listing.
-/

namespace Lax458700Proofs

universe u

variable {V : Type u}

/-- A vertex together with its layer in a `t`-string digraph. -/
abbrev StringVertex (V : Type u) (t : ℕ) := V × Fin t

/-- The edge relation of the `t`-string digraph of `rel`. -/
def stringRel (rel : V → V → Prop) {t : ℕ} :
    StringVertex V t → StringVertex V t → Prop :=
  fun source target ↦
    (source.2 = target.2 ∧ rel source.1 target.1) ∨
      (source.2 < target.2 ∧ rel target.1 source.1)

/-- Add one directed precedence constraint to a relation. -/
def withEdge {A : Type*} (rel : A → A → Prop) (earlier later : A) : A → A → Prop :=
  fun source target ↦ rel source target ∨ source = earlier ∧ target = later

theorem stringRel_sameLayer (rel : V → V → Prop) {t : ℕ}
    {left right : V} (hedge : rel left right) (layer : Fin t) :
    stringRel rel (left, layer) (right, layer) :=
  Or.inl ⟨rfl, hedge⟩

theorem stringRel_crossLayer (rel : V → V → Prop) {t : ℕ}
    {left right : V} (hedge : rel left right) {earlier later : Fin t}
    (hlayers : earlier < later) :
    stringRel rel (right, earlier) (left, later) :=
  Or.inr ⟨hlayers, hedge⟩

/-- A finite topological listing records every vertex exactly once and puts every source
of a relation edge before its target. -/
structure TopologicalListing {α : Type u} [BEq α] [LawfulBEq α]
    (rel : α → α → Prop) where
  order : List α
  nodup : order.Nodup
  complete : ∀ vertex : α, vertex ∈ order
  respects : ∀ {source target : α}, rel source target →
    order.idxOf source < order.idxOf target

namespace TopologicalListing

variable {α : Type u} [Fintype α] [BEq α] [LawfulBEq α]
    {rel : α → α → Prop}

omit [Fintype α] in
theorem mem_iff (listing : TopologicalListing rel) (vertex : α) :
    vertex ∈ listing.order ↔ True := ⟨fun _ ↦ trivial, fun _ ↦ listing.complete vertex⟩

/-- A topological listing is a permutation of the canonical finite enumeration. -/
theorem perm_univ (listing : TopologicalListing rel) :
    listing.order.Perm Finset.univ.toList := by
  apply (List.perm_ext_iff_of_nodup listing.nodup (Finset.univ.nodup_toList)).mpr
  intro vertex
  simp [listing.complete]

omit [Fintype α] in
/-- A listing for a stronger relation is also a listing for every subrelation. -/
def mono {stronger : α → α → Prop} (listing : TopologicalListing stronger)
    (hsub : ∀ ⦃source target⦄, rel source target → stronger source target) :
    TopologicalListing rel :=
  { order := listing.order
    nodup := listing.nodup
    complete := listing.complete
    respects := fun hedge ↦ listing.respects (hsub hedge) }

omit [Fintype α] in
/-- In a pairwise ordered list, a strict relation between two present, distinct entries
forces the corresponding order of their indices. -/
theorem pairwise_idxOf_lt {order : List α} {s : α → α → Prop}
    (horder : order.Pairwise s) (hantisymm : ∀ ⦃a b⦄, s a b → s b a → a = b)
    {a b : α} (ha : a ∈ order) (hb : b ∈ order) (hab : s a b) (hne : a ≠ b) :
    order.idxOf a < order.idxOf b := by
  have hapos : order.idxOf a < order.length := List.idxOf_lt_length_of_mem ha
  have hbpos : order.idxOf b < order.length := List.idxOf_lt_length_of_mem hb
  have hidxne : order.idxOf a ≠ order.idxOf b := by
    intro heq
    exact hne ((List.idxOf_inj ha).mp heq)
  by_contra hnot
  have hreverse : order.idxOf b < order.idxOf a := by omega
  have hba := horder.rel_get_of_lt
    (a := ⟨order.idxOf b, hbpos⟩) (b := ⟨order.idxOf a, hapos⟩) hreverse
  rw [List.idxOf_get hbpos, List.idxOf_get hapos] at hba
  exact hne (hantisymm hab hba)

/-- Every finite acyclic relation has a complete topological listing. The construction
linearly extends its reflexive-transitive closure and sorts the finite universe. -/
noncomputable def ofAcyclic {rel : α → α → Prop}
    (hacyclic : ∀ vertex, ¬Relation.TransGen rel vertex vertex) :
    TopologicalListing rel := by
  let closure : α → α → Prop := Relation.ReflTransGen rel
  letI : IsPartialOrder α closure :=
    { refl := fun _ ↦ Relation.ReflTransGen.refl
      trans := fun _ _ _ ↦ Relation.ReflTransGen.trans
      antisymm := fun a b hab hba ↦ by
        by_contra hne
        have hab' : Relation.TransGen rel a b :=
          (Relation.reflTransGen_iff_eq_or_transGen.mp hab).resolve_left
            (fun h ↦ hne h.symm)
        have hba' : Relation.TransGen rel b a :=
          (Relation.reflTransGen_iff_eq_or_transGen.mp hba).resolve_left hne
        exact hacyclic a (hab'.trans hba') }
  choose linear hlinear hextends using extend_partialOrder closure
  letI : IsLinearOrder α linear := hlinear
  letI : DecidableRel linear := Classical.decRel linear
  let order := Finset.univ.sort linear
  refine
    { order := order
      nodup := Finset.sort_nodup _ _
      complete := ?_
      respects := ?_ }
  · intro vertex
    simp [order]
  · intro source target hedge
    have hne : source ≠ target := by
      intro heq
      subst target
      exact hacyclic source (.single hedge)
    have hforward : linear source target :=
      hextends source target (Relation.ReflTransGen.single hedge)
    exact pairwise_idxOf_lt (Finset.pairwise_sort _ linear)
      (fun _ _ ↦ antisymm) (by simp) (by simp) hforward hne

set_option linter.style.haveILetI false in
/-- A finite DAG has a topological listing placing `earlier` before `later` whenever
`later` cannot reach `earlier`. This is the constrained-sort primitive used by the
non-edge half of the string-digraph construction. -/
theorem exists_ofAcyclic_with_before {rel : α → α → Prop}
    (hacyclic : ∀ vertex, ¬Relation.TransGen rel vertex vertex)
    (earlier later : α)
    (hnot : ¬Relation.ReflTransGen rel later earlier) :
    ∃ listing : TopologicalListing rel,
      listing.order.idxOf earlier < listing.order.idxOf later := by
  let closure : α → α → Prop := Relation.ReflTransGen rel
  letI : IsPartialOrder α closure :=
    { refl := fun _ ↦ Relation.ReflTransGen.refl
      trans := fun _ _ _ ↦ Relation.ReflTransGen.trans
      antisymm := fun a b hab hba ↦ by
        by_contra hne
        have hab' : Relation.TransGen rel a b :=
          (Relation.reflTransGen_iff_eq_or_transGen.mp hab).resolve_left
            (fun h ↦ hne h.symm)
        have hba' : Relation.TransGen rel b a :=
          (Relation.reflTransGen_iff_eq_or_transGen.mp hba).resolve_left hne
        exact hacyclic a (hab'.trans hba') }
  let forced : α → α → Prop := fun x y ↦
    closure x y ∨ closure x earlier ∧ closure later y
  letI : IsPartialOrder α forced :=
    { refl := fun _ ↦ Or.inl (refl _)
      trans := fun a b c hab hbc ↦ by
        rcases hab with hab | ⟨hae, hlb⟩
        · rcases hbc with hbc | ⟨hbe, hlc⟩
          · exact Or.inl (Relation.ReflTransGen.trans hab hbc)
          · exact Or.inr ⟨Relation.ReflTransGen.trans hab hbe, hlc⟩
        · rcases hbc with hbc | ⟨_, hlc⟩
          · exact Or.inr ⟨hae, Relation.ReflTransGen.trans hlb hbc⟩
          · exact Or.inr ⟨hae, hlc⟩
      antisymm := fun a b hab hba ↦ by
        rcases hab with hab | ⟨hae, hlb⟩
        · rcases hba with hba | ⟨hbe, hla⟩
          · exact antisymm hab hba
          · exact (hnot (Relation.ReflTransGen.trans hla
              (Relation.ReflTransGen.trans hab hbe))).elim
        · rcases hba with hba | ⟨hbe, hla⟩
          · exact (hnot (Relation.ReflTransGen.trans hlb
              (Relation.ReflTransGen.trans hba hae))).elim
          · exact (hnot (Relation.ReflTransGen.trans hla hae)).elim }
  choose linear hlinear hextends using extend_partialOrder forced
  letI : IsLinearOrder α linear := hlinear
  letI : DecidableRel linear := Classical.decRel linear
  let order := Finset.univ.sort linear
  let listing : TopologicalListing rel :=
    { order := order
      nodup := Finset.sort_nodup _ _
      complete := by intro vertex; simp [order]
      respects := by
        intro source target hedge
        have hne : source ≠ target := by
          intro heq
          subst target
          exact hacyclic source (.single hedge)
        have hforward : linear source target :=
          hextends source target (Or.inl (Relation.ReflTransGen.single hedge))
        exact pairwise_idxOf_lt (Finset.pairwise_sort _ linear)
          (fun _ _ ↦ antisymm) (by simp) (by simp) hforward hne }
  refine ⟨listing, ?_⟩
  have hne : earlier ≠ later := by
    intro heq
    subst later
    exact hnot Relation.ReflTransGen.refl
  have hforced : forced earlier later :=
    Or.inr ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  have hforward : linear earlier later := hextends earlier later hforced
  exact pairwise_idxOf_lt (Finset.pairwise_sort _ linear)
    (fun _ _ ↦ antisymm) (by simp) (by simp) hforward hne

/-- Adding one precedence edge preserves acyclicity exactly when its target cannot
already reach its source. The proof uses a constrained topological listing as a
strict natural-valued ranking. -/
theorem withEdge_acyclic {rel : α → α → Prop}
    (hacyclic : ∀ vertex, ¬Relation.TransGen rel vertex vertex)
    (earlier later : α)
    (hnot : ¬Relation.ReflTransGen rel later earlier) :
    ∀ vertex, ¬Relation.TransGen (withEdge rel earlier later) vertex vertex := by
  obtain ⟨listing, hbefore⟩ :=
    exists_ofAcyclic_with_before hacyclic earlier later hnot
  intro vertex cycle
  have hedgeOrder : ∀ {source target : α}, withEdge rel earlier later source target →
      listing.order.idxOf source < listing.order.idxOf target := by
    intro source target hedge
    rcases hedge with hedge | ⟨rfl, rfl⟩
    · exact listing.respects hedge
    · exact hbefore
  have orderPath : ∀ {target : α},
      Relation.TransGen (withEdge rel earlier later) vertex target →
        listing.order.idxOf vertex < listing.order.idxOf target := by
    intro target path
    induction path with
    | single hedge => exact hedgeOrder hedge
    | tail _ hedge ih => exact ih.trans (hedgeOrder hedge)
  exact Nat.lt_irrefl _ (orderPath cycle)

omit [Fintype α] in
/-- A topological listing respects every nonempty path, not only individual edges. -/
theorem respects_transGen (listing : TopologicalListing rel)
    {source target : α} (path : Relation.TransGen rel source target) :
    listing.order.idxOf source < listing.order.idxOf target := by
  induction path with
  | single hedge => exact listing.respects hedge
  | tail _ hedge ih => exact ih.trans (listing.respects hedge)

end TopologicalListing

/-- Every string edge weakly increases its layer. -/
theorem stringRel_layer_le {rel : V → V → Prop} {t : ℕ}
    {source target : StringVertex V t} (hedge : stringRel rel source target) :
    source.2 ≤ target.2 := by
  rcases hedge with ⟨hsame, _⟩ | ⟨hlt, _⟩
  · exact hsame.le
  · exact hlt.le

/-- Every nonempty string path weakly increases its layer. -/
theorem stringRel_transGen_layer_le {rel : V → V → Prop} {t : ℕ}
    {source target : StringVertex V t}
    (path : Relation.TransGen (stringRel rel) source target) :
    source.2 ≤ target.2 := by
  induction path with
  | single hedge => exact stringRel_layer_le hedge
  | tail path hedge ih => exact ih.trans (stringRel_layer_le hedge)

/-- A string path whose endpoints lie in the same layer projects to a nonempty path in
the original relation. -/
theorem stringRel_transGen_fst_of_snd_eq
    {rel : V → V → Prop} {t : ℕ}
    {source target : StringVertex V t}
    (path : Relation.TransGen (stringRel rel) source target)
    (hlayer : source.2 = target.2) :
    Relation.TransGen rel source.1 target.1 := by
  induction path with
  | single hedge =>
      rcases hedge with ⟨_, hrel⟩ | ⟨hlt, _⟩
      · exact .single hrel
      · exact (hlt.ne hlayer).elim
  | @tail middle target path hedge ih =>
      have hsourceMiddle : source.2 ≤ middle.2 :=
        stringRel_transGen_layer_le path
      have hmiddleTarget : middle.2 ≤ target.2 := stringRel_layer_le hedge
      have hsourceMiddleEq : source.2 = middle.2 := by omega
      have hmiddleTargetEq : middle.2 = target.2 := by omega
      have hfirst : Relation.TransGen rel source.1 middle.1 := ih hsourceMiddleEq
      have hlast : rel middle.1 target.1 := by
        rcases hedge with ⟨_, hrel⟩ | ⟨hlt, _⟩
        · exact hrel
        · exact (hlt.ne hmiddleTargetEq).elim
      exact hfirst.tail hlast

/-- The string digraph of an acyclic relation is acyclic. A cycle cannot increase its
layer, so it would project to a cycle in the original relation. -/
theorem stringRel_acyclic {rel : V → V → Prop} {t : ℕ}
    (hacyclic : ∀ vertex, ¬Relation.TransGen rel vertex vertex) :
    ∀ vertex, ¬Relation.TransGen (@stringRel V rel t) vertex vertex := by
  intro vertex cycle
  exact hacyclic vertex.1 (stringRel_transGen_fst_of_snd_eq cycle rfl)

/-- In the two-string digraph, each endpoint of an original edge has its first copy
before its second copy. -/
theorem stringRel_two_copy_paths_of_edge {rel : V → V → Prop}
    {left right : V} (hedge : rel left right) :
    Relation.TransGen (@stringRel V rel 2) (left, 0) (left, 1) ∧
      Relation.TransGen (@stringRel V rel 2) (right, 0) (right, 1) := by
  constructor
  · exact (Relation.TransGen.single (stringRel_sameLayer rel hedge 0)).tail
      (stringRel_crossLayer rel hedge (by decide))
  · exact (Relation.TransGen.single (stringRel_crossLayer rel hedge (by decide))).tail
      (stringRel_sameLayer rel hedge 1)

/-- More generally, the endpoints of every nonempty original directed path have their
two copies in occurrence order. -/
theorem stringRel_two_copy_paths_of_transGen {rel : V → V → Prop}
    {left right : V} (path : Relation.TransGen rel left right) :
    Relation.TransGen (@stringRel V rel 2) (left, 0) (left, 1) ∧
      Relation.TransGen (@stringRel V rel 2) (right, 0) (right, 1) := by
  induction path with
  | single hedge => exact stringRel_two_copy_paths_of_edge hedge
  | tail _ hedge ih => exact ⟨ih.1, (stringRel_two_copy_paths_of_edge hedge).2⟩

/-- A path starting in layer zero of a two-string digraph either stays in layer zero,
where it projects to the original relation, or crosses exactly once. In the latter case
the crossing exposes a reversed original edge `y → x`, with original reachability from
the start to `x` and from `y` to the finish. -/
theorem two_string_path_from_zero {rel : V → V → Prop}
    {start : V} {target : StringVertex V 2}
    (path : Relation.TransGen (@stringRel V rel 2) (start, 0) target) :
    (target.2 = 0 ∧ Relation.TransGen rel start target.1) ∨
      (target.2 = 1 ∧ ∃ x y : V,
        Relation.ReflTransGen rel start x ∧ rel y x ∧
          Relation.ReflTransGen rel y target.1) := by
  induction path with
  | @single target hedge =>
      rcases hedge with ⟨hsame, hrel⟩ | ⟨hlt, hrel⟩
      · exact Or.inl ⟨hsame.symm, .single hrel⟩
      · refine Or.inr ⟨?_, start, target.1, .refl, hrel, .refl⟩
        omega
  | @tail middle target path hedge ih =>
      rcases ih with ⟨hmiddle, hpath⟩ | ⟨hmiddle, x, y, hstart, hyx, hymiddle⟩
      · rcases hedge with ⟨hsame, hrel⟩ | ⟨hlt, hrel⟩
        · exact Or.inl ⟨hmiddle.symm.trans hsame |>.symm, hpath.tail hrel⟩
        · refine Or.inr ⟨?_, middle.1, target.1,
            hpath.to_reflTransGen, hrel, .refl⟩
          omega
      · rcases hedge with ⟨hsame, hrel⟩ | ⟨hlt, _⟩
        · exact Or.inr ⟨hmiddle.symm.trans hsame |>.symm, x, y,
            hstart, hyx, hymiddle.tail hrel⟩
        · omega

/-- Specialized crossing decomposition for a path from a first copy to a second copy. -/
theorem two_string_cross_decompose {rel : V → V → Prop} {start finish : V}
    (path : Relation.TransGen (@stringRel V rel 2) (start, 0) (finish, 1)) :
    ∃ x y : V,
      Relation.ReflTransGen rel start x ∧ rel y x ∧
        Relation.ReflTransGen rel y finish := by
  rcases two_string_path_from_zero path with ⟨hzero, _⟩ | ⟨_, result⟩
  · simp at hzero
  · exact result

namespace StringTopologicalListing

variable [DecidableEq V] {rel : V → V → Prop} {t : ℕ}

/-- The canonical existence witness: an acyclic finite relation has a topological listing
of each of its string digraphs. -/
noncomputable def ofAcyclic [Fintype V]
    (hacyclic : ∀ vertex, ¬Relation.TransGen rel vertex vertex) :
    TopologicalListing (@stringRel V rel t) :=
  TopologicalListing.ofAcyclic (stringRel_acyclic hacyclic)

/-- Forget layer indices in a topological listing of a string digraph. -/
def erasedWord (listing : TopologicalListing (@stringRel V rel t)) : Word V :=
  listing.order.map Prod.fst

theorem erasedWord_covers (listing : TopologicalListing (@stringRel V rel t))
    (ht : 0 < t) : (erasedWord listing).Covers := by
  intro vertex
  let layer : Fin t := ⟨0, ht⟩
  exact List.mem_map.mpr ⟨(vertex, layer), listing.complete (vertex, layer), rfl⟩

/-- Erasing the layer indices from a complete listing gives exactly `t` copies of
each original vertex. -/
theorem erasedWord_uniform [Fintype V]
    (listing : TopologicalListing (@stringRel V rel t)) :
    (erasedWord listing).IsUniform t := by
  intro vertex
  have hbase : List.Perm listing.order
      (Finset.univ.toList : List (V × Fin t)) :=
    TopologicalListing.perm_univ (rel := @stringRel V rel t) listing
  have hperm : List.Perm (listing.order.map Prod.fst)
      (Finset.univ.toList.map (fun item : V × Fin t ↦ item.1)) :=
    hbase.map Prod.fst
  rw [erasedWord, hperm.count_eq]
  rw [List.count, List.countP_map]
  change List.countP (fun item : V × Fin t ↦ decide (item.1 = vertex))
      Finset.univ.toList = t
  rw [← Finset.univ.nodup_toList.card_eq_countP, Finset.toList_toFinset]
  have hfiber : (Finset.univ.filter fun item : V × Fin t ↦ item.1 = vertex) =
      {vertex} ×ˢ (Finset.univ : Finset (Fin t)) := by
    ext item
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
    exact (and_iff_left_of_imp fun _ ↦ trivial).symm
  rw [hfiber, Finset.card_product]
  simp

/-- Same-layer copies of an oriented edge occur in the directed order. -/
theorem sameLayer_order (listing : TopologicalListing (@stringRel V rel t))
    {left right : V} (hedge : rel left right) (layer : Fin t) :
    listing.order.idxOf (left, layer) < listing.order.idxOf (right, layer) :=
  listing.respects (stringRel_sameLayer rel hedge layer)

/-- A target copy in an earlier layer occurs before the source copy in a later layer. -/
theorem crossLayer_order (listing : TopologicalListing (@stringRel V rel t))
    {left right : V} (hedge : rel left right) {earlier later : Fin t}
    (hlayers : earlier < later) :
    listing.order.idxOf (right, earlier) < listing.order.idxOf (left, later) :=
  listing.respects (stringRel_crossLayer rel hedge hlayers)

/-- If copies of a vertex appear in increasing layer order, then exactly `layer` copies
of that vertex precede its copy in `layer`. -/
theorem countBefore_eq_layer
    (listing : TopologicalListing (@stringRel V rel t))
    (vertex : V) (layer : Fin t)
    (hmono : ∀ {earlier later : Fin t}, earlier < later →
      listing.order.idxOf (vertex, earlier) <
        listing.order.idxOf (vertex, later)) :
    (erasedWord listing).countBefore vertex
        (listing.order.idxOf (vertex, layer)) = layer.val := by
  rw [erasedWord, List.countBefore_eq_count_take]
  rw [← List.map_take]
  rw [List.count, List.countP_map]
  change List.countP (fun item : V × Fin t ↦ decide (item.1 = vertex))
      (listing.order.take (listing.order.idxOf (vertex, layer))) = layer.val
  have hprefixNodup :
      (listing.order.take (listing.order.idxOf (vertex, layer))).Nodup :=
    listing.nodup.take
  have hcard := hprefixNodup.card_eq_countP
    (P := fun item : V × Fin t ↦ item.1 = vertex)
  rw [← hcard]
  have hfilter :
      ((listing.order.take (listing.order.idxOf (vertex, layer))).toFinset.filter
        fun item : V × Fin t ↦ item.1 = vertex) =
      {vertex} ×ˢ Finset.Iio layer := by
    ext item
    rcases item with ⟨itemVertex, itemLayer⟩
    simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_product,
      Finset.mem_singleton, Finset.mem_Iio]
    constructor
    · rintro ⟨hmem, hvertex⟩
      subst itemVertex
      have hpos : listing.order.idxOf (vertex, itemLayer) <
          listing.order.idxOf (vertex, layer) :=
        (List.mem_take_iff_idxOf_lt (listing.complete (vertex, itemLayer))).mp hmem
      refine ⟨rfl, ?_⟩
      by_contra hnot
      have hle : layer ≤ itemLayer := le_of_not_gt hnot
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact (Nat.not_lt_of_ge (Nat.le_of_lt (hmono hlt))) hpos
      · subst itemLayer
        exact Nat.lt_irrefl _ hpos
    · rintro ⟨hvertex, hlayer⟩
      subst itemVertex
      refine ⟨?_, rfl⟩
      exact (List.mem_take_iff_idxOf_lt (listing.complete (vertex, itemLayer))).mpr
        (hmono hlayer)
  rw [hfilter, Finset.card_product, Fin.card_Iio]
  simp

/-- Under increasing layer order, occurrence number and layer number agree. -/
theorem idxOfNth_eq_layer
    (listing : TopologicalListing (@stringRel V rel t))
    (vertex : V) (layer : Fin t)
    (hmono : ∀ {earlier later : Fin t}, earlier < later →
      listing.order.idxOf (vertex, earlier) <
        listing.order.idxOf (vertex, later)) :
    (erasedWord listing).idxOfNth vertex layer.val =
      listing.order.idxOf (vertex, layer) := by
  have hpOrder : listing.order.idxOf (vertex, layer) < listing.order.length :=
    List.idxOf_lt_length_of_mem (listing.complete (vertex, layer))
  have hpWord : listing.order.idxOf (vertex, layer) < (erasedWord listing).length := by
    simpa [erasedWord] using hpOrder
  have hletter : (erasedWord listing)[listing.order.idxOf (vertex, layer)] = vertex := by
    simp only [erasedWord, List.getElem_map]
    rw [List.getElem_idxOf hpOrder]
  have hbeq : (erasedWord listing)[listing.order.idxOf (vertex, layer)] == vertex := by
    rw [hletter]
    exact BEq.rfl
  have hposition := List.idxOfNth_countBefore_of_lt_length_of_beq
    (xs := erasedWord listing) (x := vertex) (i := listing.order.idxOf (vertex, layer))
    (h := hpWord) hbeq
  rw [countBefore_eq_layer listing vertex layer hmono] at hposition
  exact hposition

/-- The source copies of an oriented edge occur in increasing layer order. -/
theorem sourceLayer_order
    (listing : TopologicalListing (@stringRel V rel t))
    {left right : V} (hedge : rel left right)
    {earlier later : Fin t} (hlayers : earlier < later) :
    listing.order.idxOf (left, earlier) <
      listing.order.idxOf (left, later) :=
  (sameLayer_order listing hedge earlier).trans
    (crossLayer_order listing hedge hlayers)

/-- The target copies of an oriented edge occur in increasing layer order. -/
theorem targetLayer_order
    (listing : TopologicalListing (@stringRel V rel t))
    {left right : V} (hedge : rel left right)
    {earlier later : Fin t} (hlayers : earlier < later) :
    listing.order.idxOf (right, earlier) <
      listing.order.idxOf (right, later) :=
  (crossLayer_order listing hedge hlayers).trans
    (sameLayer_order listing hedge later)

/-- Every original oriented edge has the exact repeated `left right` pattern in the word
obtained from a topological listing of the string digraph. -/
theorem restrictToPair_eq_alternatingPairs_of_rel [Fintype V]
    (listing : TopologicalListing (@stringRel V rel t))
    {left right : V} (hne : left ≠ right) (hedge : rel left right) :
    (erasedWord listing).restrictToPair left right =
      alternatingPairs left right t := by
  have hsource : ∀ {earlier later : Fin t}, earlier < later →
      listing.order.idxOf (left, earlier) <
        listing.order.idxOf (left, later) := by
    intro earlier later hlayers
    exact sourceLayer_order listing hedge hlayers
  have htarget : ∀ {earlier later : Fin t}, earlier < later →
      listing.order.idxOf (right, earlier) <
        listing.order.idxOf (right, later) := by
    intro earlier later hlayers
    exact targetLayer_order listing hedge hlayers
  have hsame : ∀ n, n < t →
      (erasedWord listing).idxOfNth left n <
        (erasedWord listing).idxOfNth right n := by
    intro n hn
    let layer : Fin t := ⟨n, hn⟩
    rw [idxOfNth_eq_layer listing left layer hsource,
      idxOfNth_eq_layer listing right layer htarget]
    exact sameLayer_order listing hedge layer
  have hnext : ∀ n, n + 1 < t →
      (erasedWord listing).idxOfNth right n <
        (erasedWord listing).idxOfNth left (n + 1) := by
    intro n hn
    let earlier : Fin t := ⟨n, by omega⟩
    let later : Fin t := ⟨n + 1, hn⟩
    rw [idxOfNth_eq_layer listing right earlier htarget,
      idxOfNth_eq_layer listing left later hsource]
    exact crossLayer_order listing hedge (by simp [earlier, later])
  have huniform := erasedWord_uniform listing
  exact restrictToPair_eq_alternatingPairs_of_occurrence_interleaving
    hne (huniform left) (huniform right) hsame hnext

/-- Every original oriented edge alternates in the word obtained from any topological
listing of the string digraph. This is the edge half of the HKP string-digraph lemma. -/
theorem lettersAlternate_of_rel [Fintype V]
    (listing : TopologicalListing (@stringRel V rel t))
    {left right : V} (hne : left ≠ right) (hedge : rel left right) :
    LettersAlternate (erasedWord listing) left right := by
  have hpattern := restrictToPair_eq_alternatingPairs_of_rel listing hne hedge
  exact ⟨hne, by rw [hpattern]; exact isAlternating_alternatingPairs hne t⟩

/-- An acyclic finite relation therefore supplies a `t`-uniform word in which every
distinct related pair alternates. -/
theorem exists_uniform_word_of_acyclic [Fintype V]
    (hacyclic : ∀ vertex, ¬Relation.TransGen rel vertex vertex) :
    ∃ word : Word V,
      word.IsUniform t ∧
        ∀ ⦃left right : V⦄, left ≠ right → rel left right →
          LettersAlternate word left right := by
  let listing : TopologicalListing (@stringRel V rel t) := ofAcyclic hacyclic
  exact ⟨erasedWord listing, erasedWord_uniform listing,
    fun {_ _} hne hedge ↦ lettersAlternate_of_rel listing hne hedge⟩

/-- Ordering half of the comparable non-edge case in HKP Lemma 11. If `left` reaches
`right` in the original DAG but the first copy of `right` cannot reach the second copy
of `left`, a constrained topological listing gives a 2-uniform word that preserves every
original arc while making `left` and `right` fail to alternate. Semi-transitivity will
supply the no-reachability hypothesis. -/
theorem exists_two_uniform_separating_word_of_reachable [Fintype V]
    (hacyclic : ∀ vertex, ¬Relation.TransGen rel vertex vertex)
    {left right : V} (hne : left ≠ right)
    (hpath : Relation.TransGen rel left right)
    (hnot : ¬Relation.ReflTransGen (@stringRel V rel 2) (right, 0) (left, 1)) :
    ∃ word : Word V,
      word.IsUniform 2 ∧
        (∀ ⦃u v : V⦄, u ≠ v → rel u v →
          word.restrictToPair u v = alternatingPairs u v 2) ∧
          ¬LettersAlternate word left right := by
  obtain ⟨listing, hmiddle⟩ := TopologicalListing.exists_ofAcyclic_with_before
    (stringRel_acyclic (t := 2) hacyclic) (left, 1) (right, 0) hnot
  let word := erasedWord listing
  have hcopy := stringRel_two_copy_paths_of_transGen hpath
  have hleftOrder : listing.order.idxOf (left, 0) < listing.order.idxOf (left, 1) :=
    listing.respects_transGen hcopy.1
  have hrightOrder : listing.order.idxOf (right, 0) < listing.order.idxOf (right, 1) :=
    listing.respects_transGen hcopy.2
  have hleftMono : ∀ {earlier later : Fin 2}, earlier < later →
      listing.order.idxOf (left, earlier) < listing.order.idxOf (left, later) := by
    intro earlier later hlayers
    have he : earlier = 0 := by omega
    have hl : later = 1 := by omega
    simpa [he, hl] using hleftOrder
  have hrightMono : ∀ {earlier later : Fin 2}, earlier < later →
      listing.order.idxOf (right, earlier) < listing.order.idxOf (right, later) := by
    intro earlier later hlayers
    have he : earlier = 0 := by omega
    have hl : later = 1 := by omega
    simpa [he, hl] using hrightOrder
  have hleft0 := idxOfNth_eq_layer listing left (0 : Fin 2) hleftMono
  have hleft1 := idxOfNth_eq_layer listing left (1 : Fin 2) hleftMono
  have hright0 := idxOfNth_eq_layer listing right (0 : Fin 2) hrightMono
  have hleft0' : (erasedWord listing).idxOfNth left 0 =
      listing.order.idxOf (left, 0) := by simpa using hleft0
  have hleft1' : (erasedWord listing).idxOfNth left 1 =
      listing.order.idxOf (left, 1) := by simpa using hleft1
  have hright0' : (erasedWord listing).idxOfNth right 0 =
      listing.order.idxOf (right, 0) := by simpa using hright0
  refine ⟨word, erasedWord_uniform listing, ?_, ?_⟩
  · intro u v huv hedge
    exact restrictToPair_eq_alternatingPairs_of_rel listing huv hedge
  · intro halternate
    have hfirst : word.idxOf left < word.idxOf right := by
      change (erasedWord listing).idxOf left < (erasedWord listing).idxOf right
      rw [← List.idxOfNth_zero, ← List.idxOfNth_zero]
      rw [hleft0', hright0']
      exact hleftOrder.trans hmiddle
    have hpattern := restrictToPair_eq_alternatingPairs hne (by decide)
      (erasedWord_uniform listing left) (erasedWord_uniform listing right)
      halternate hfirst
    have hinter := occurrence_interleaving_of_restrict_eq hne hpattern 0 (by decide)
    have hvBeforeU : word.idxOfNth right 0 < word.idxOfNth left 1 :=
      hinter.2 (by decide)
    change (erasedWord listing).idxOfNth right 0 <
      (erasedWord listing).idxOfNth left 1 at hvBeforeU
    rw [hright0', hleft1'] at hvBeforeU
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hmiddle)) hvBeforeU

/-- Two vertices incomparable in the original DAG can be separated while every original
arc is preserved. We safely add the precedence chain
`u⁰ < v⁰ < v¹ < u¹` to the two-string digraph; after erasing layers this forces
the nonalternating pattern `u v v u`. -/
theorem exists_two_uniform_separating_word_of_incomparable [Fintype V]
    (hacyclic : ∀ vertex, ¬Relation.TransGen rel vertex vertex)
    {u v : V}
    (huv : ¬Relation.ReflTransGen rel u v)
    (hvu : ¬Relation.ReflTransGen rel v u) :
    ∃ word : Word V,
      word.IsUniform 2 ∧
        (∀ {left right : V}, left ≠ right → rel left right →
          word.restrictToPair left right = alternatingPairs left right 2) ∧
        ¬LettersAlternate word u v := by
  have hne : u ≠ v := by
    intro heq
    subst v
    exact huv Relation.ReflTransGen.refl
  let r0 : StringVertex V 2 → StringVertex V 2 → Prop := @stringRel V rel 2
  let r1 := withEdge r0 (u, 0) (v, 0)
  let r2 := withEdge r1 (v, 0) (v, 1)
  let r3 := withEdge r2 (v, 1) (u, 1)
  have hacyclic0 : ∀ vertex, ¬Relation.TransGen r0 vertex vertex := by
    simpa [r0] using stringRel_acyclic (t := 2) hacyclic
  have hnot1 : ¬Relation.ReflTransGen r0 (v, 0) (u, 0) := by
    intro hreach
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hreach with heq | path
    · exact hne (congrArg Prod.fst heq)
    · exact hvu (stringRel_transGen_fst_of_snd_eq path rfl).to_reflTransGen
  have hacyclic1 : ∀ vertex, ¬Relation.TransGen r1 vertex vertex := by
    simpa [r1] using TopologicalListing.withEdge_acyclic hacyclic0 (u, 0) (v, 0) hnot1
  have r1_layer_le {source target : StringVertex V 2} (hedge : r1 source target) :
      source.2 ≤ target.2 := by
    rcases hedge with hedge | ⟨rfl, rfl⟩
    · exact stringRel_layer_le hedge
    · simp
  have r1_reflTransGen_layer_le {source target : StringVertex V 2}
      (path : Relation.ReflTransGen r1 source target) : source.2 ≤ target.2 := by
    induction path with
    | refl => rfl
    | tail _ hedge ih => exact ih.trans (r1_layer_le hedge)
  have hnot2 : ¬Relation.ReflTransGen r1 (v, 1) (v, 0) := by
    intro hreach
    have hbad : (1 : Fin 2) ≤ 0 := r1_reflTransGen_layer_le hreach
    exact Nat.not_succ_le_zero 0 hbad
  have hacyclic2 : ∀ vertex, ¬Relation.TransGen r2 vertex vertex := by
    simpa [r2] using TopologicalListing.withEdge_acyclic hacyclic1 (v, 0) (v, 1) hnot2
  have r2_layer_le {source target : StringVertex V 2} (hedge : r2 source target) :
      source.2 ≤ target.2 := by
    rcases hedge with hedge | ⟨rfl, rfl⟩
    · exact r1_layer_le hedge
    · simp
  have r2_reflTransGen_layer_le {source target : StringVertex V 2}
      (path : Relation.ReflTransGen r2 source target) : source.2 ≤ target.2 := by
    induction path with
    | refl => rfl
    | tail _ hedge ih => exact ih.trans (r2_layer_le hedge)
  have r2_same_layer_one {source target : StringVertex V 2}
      (hedge : r2 source target) (hsource : source.2 = 1) (htarget : target.2 = 1) :
      rel source.1 target.1 := by
    rcases hedge with hedge | ⟨rfl, rfl⟩
    · rcases hedge with hedge | ⟨rfl, rfl⟩
      · rcases hedge with ⟨_, hrel⟩ | ⟨hlayer, _⟩
        · exact hrel
        · omega
      · simp at hsource
    · simp at hsource
  have r2_project_one {source target : StringVertex V 2}
      (path : Relation.ReflTransGen r2 source target)
      (hsource : source.2 = 1) (htarget : target.2 = 1) :
      Relation.ReflTransGen rel source.1 target.1 := by
    induction path with
    | refl => exact Relation.ReflTransGen.refl
    | @tail middle target path hedge ih =>
        have hsourceMiddle := r2_reflTransGen_layer_le path
        have hmiddleTarget := r2_layer_le hedge
        have hmiddle : middle.2 = 1 := by omega
        exact (ih hmiddle).tail (r2_same_layer_one hedge hmiddle htarget)
  have hnot3 : ¬Relation.ReflTransGen r2 (u, 1) (v, 1) := by
    intro hreach
    exact huv (r2_project_one hreach rfl rfl)
  have hacyclic3 : ∀ vertex, ¬Relation.TransGen r3 vertex vertex := by
    simpa [r3] using TopologicalListing.withEdge_acyclic hacyclic2 (v, 1) (u, 1) hnot3
  let strong : TopologicalListing r3 := TopologicalListing.ofAcyclic hacyclic3
  let listing : TopologicalListing r0 := strong.mono fun {_ _} hedge ↦
    Or.inl (Or.inl (Or.inl hedge))
  have hu0v0 : listing.order.idxOf (u, 0) < listing.order.idxOf (v, 0) := by
    change strong.order.idxOf (u, 0) < strong.order.idxOf (v, 0)
    exact strong.respects
      (show r3 (u, 0) (v, 0) from Or.inl (Or.inl (Or.inr ⟨rfl, rfl⟩)))
  have hv0v1 : listing.order.idxOf (v, 0) < listing.order.idxOf (v, 1) := by
    change strong.order.idxOf (v, 0) < strong.order.idxOf (v, 1)
    exact strong.respects
      (show r3 (v, 0) (v, 1) from Or.inl (Or.inr ⟨rfl, rfl⟩))
  have hv1u1 : listing.order.idxOf (v, 1) < listing.order.idxOf (u, 1) := by
    change strong.order.idxOf (v, 1) < strong.order.idxOf (u, 1)
    exact strong.respects
      (show r3 (v, 1) (u, 1) from Or.inr ⟨rfl, rfl⟩)
  have hu0u1 : listing.order.idxOf (u, 0) < listing.order.idxOf (u, 1) :=
    hu0v0.trans (hv0v1.trans hv1u1)
  have huMono : ∀ {earlier later : Fin 2}, earlier < later →
      listing.order.idxOf (u, earlier) < listing.order.idxOf (u, later) := by
    intro earlier later hlayers
    have he : earlier = 0 := by omega
    have hl : later = 1 := by omega
    simpa [he, hl] using hu0u1
  have hvMono : ∀ {earlier later : Fin 2}, earlier < later →
      listing.order.idxOf (v, earlier) < listing.order.idxOf (v, later) := by
    intro earlier later hlayers
    have he : earlier = 0 := by omega
    have hl : later = 1 := by omega
    simpa [he, hl] using hv0v1
  let word := erasedWord listing
  refine ⟨word, erasedWord_uniform listing, ?_, ?_⟩
  · intro left right hdistinct hedge
    exact restrictToPair_eq_alternatingPairs_of_rel listing hdistinct hedge
  · intro halternate
    have hu0 := idxOfNth_eq_layer listing u (0 : Fin 2) huMono
    have hu1 := idxOfNth_eq_layer listing u (1 : Fin 2) huMono
    have hv0 := idxOfNth_eq_layer listing v (0 : Fin 2) hvMono
    have hv1 := idxOfNth_eq_layer listing v (1 : Fin 2) hvMono
    have hu0' : (erasedWord listing).idxOfNth u 0 =
        listing.order.idxOf (u, 0) := by simpa using hu0
    have hu1' : (erasedWord listing).idxOfNth u 1 =
        listing.order.idxOf (u, 1) := by simpa using hu1
    have hv0' : (erasedWord listing).idxOfNth v 0 =
        listing.order.idxOf (v, 0) := by simpa using hv0
    have hv1' : (erasedWord listing).idxOfNth v 1 =
        listing.order.idxOf (v, 1) := by simpa using hv1
    have hfirst : word.idxOf u < word.idxOf v := by
      change (erasedWord listing).idxOf u < (erasedWord listing).idxOf v
      rw [← List.idxOfNth_zero, ← List.idxOfNth_zero]
      rw [hu0', hv0']
      exact hu0v0
    have hpattern := restrictToPair_eq_alternatingPairs hne (by decide)
      (erasedWord_uniform listing u) (erasedWord_uniform listing v)
      halternate hfirst
    have hinter := occurrence_interleaving_of_restrict_eq hne hpattern 1 (by decide)
    have huBeforeV : word.idxOfNth u 1 < word.idxOfNth v 1 := hinter.1
    change (erasedWord listing).idxOfNth u 1 <
      (erasedWord listing).idxOfNth v 1 at huBeforeV
    rw [hu1', hv1'] at huBeforeV
    exact (Nat.not_lt_of_ge hv1u1.le) huBeforeV

end StringTopologicalListing

namespace SemiTransitiveOrientation

/-- Comparable nonadjacent vertices have no path from the first copy of the later
vertex to the second copy of the earlier vertex in the two-string digraph. A supposed
path exposes an original endpoint edge spanning the given reachability interval;
semi-transitivity would then force the missing graph edge. -/
theorem no_two_string_cross_reach_of_reachable_nonedge {G : SimpleGraph V}
    (orientation : SemiTransitiveOrientation G)
    {left right : V}
    (hpath : Relation.TransGen orientation.rel left right)
    (hnonedge : ¬G.Adj left right) :
    ¬Relation.ReflTransGen (@stringRel V orientation.rel 2) (right, 0) (left, 1) := by
  intro hreach
  have hdistinct : (right, (0 : Fin 2)) ≠ (left, (1 : Fin 2)) := by
    intro heq
    exact Fin.zero_ne_one (congrArg Prod.snd heq)
  have hcross : Relation.TransGen (@stringRel V orientation.rel 2)
      (right, 0) (left, 1) :=
    (Relation.reflTransGen_iff_eq_or_transGen.mp hreach).resolve_left hdistinct.symm
  rcases two_string_cross_decompose hcross with ⟨x, y, hrightX, hyx, hyLeft⟩
  have hleftRight : orientation.rel left right :=
    orientation.edge_of_reachable_interval hyLeft hpath hrightX hyx
  exact hnonedge (orientation.rel_implies_adj hleftRight)

/-- Comparable nonadjacent vertices can be separated by a 2-uniform word while every
oriented edge is still represented. This is the comparable case of HKP Lemma 11. -/
theorem exists_two_uniform_separating_word_of_reachable_nonedge
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (orientation : SemiTransitiveOrientation G)
    {left right : V}
    (hpath : Relation.TransGen orientation.rel left right)
    (hnonedge : ¬G.Adj left right) :
    ∃ word : Word V,
      word.IsUniform 2 ∧
        (∀ {u v : V}, u ≠ v → orientation.rel u v →
          word.restrictToPair u v = alternatingPairs u v 2) ∧
          ¬LettersAlternate word left right := by
  have hne : left ≠ right := by
    intro heq
    subst right
    exact orientation.acyclic left hpath
  exact StringTopologicalListing.exists_two_uniform_separating_word_of_reachable
    orientation.acyclic hne hpath
      (orientation.no_two_string_cross_reach_of_reachable_nonedge hpath hnonedge)

/-- Every distinct nonedge of a finite semi-transitively oriented graph has its own
2-uniform separating word that continues to represent every oriented edge. The proof
splits into reachability in either direction and mutual incomparability. -/
theorem exists_two_uniform_separating_word_of_nonedge
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (orientation : SemiTransitiveOrientation G)
    {left right : V} (hne : left ≠ right)
    (hnonedge : ¬G.Adj left right) :
    ∃ word : Word V,
      word.IsUniform 2 ∧
        (∀ {u v : V}, u ≠ v → orientation.rel u v →
          word.restrictToPair u v = alternatingPairs u v 2) ∧
          ¬LettersAlternate word left right := by
  by_cases hleftRight : Relation.ReflTransGen orientation.rel left right
  · have hpath : Relation.TransGen orientation.rel left right :=
      (Relation.reflTransGen_iff_eq_or_transGen.mp hleftRight).resolve_left
        (fun heq ↦ hne heq.symm)
    exact orientation.exists_two_uniform_separating_word_of_reachable_nonedge
      hpath hnonedge
  · by_cases hrightLeft : Relation.ReflTransGen orientation.rel right left
    · have hpath : Relation.TransGen orientation.rel right left :=
        (Relation.reflTransGen_iff_eq_or_transGen.mp hrightLeft).resolve_left hne
      have hnonedge' : ¬G.Adj right left := fun hedge ↦ hnonedge hedge.symm
      obtain ⟨word, huniform, hedges, hseparates⟩ :=
        orientation.exists_two_uniform_separating_word_of_reachable_nonedge
          hpath hnonedge'
      exact ⟨word, huniform, hedges,
        fun halternates ↦ hseparates ((lettersAlternate_comm word left right).mp halternates)⟩
    · exact StringTopologicalListing.exists_two_uniform_separating_word_of_incomparable
        orientation.acyclic hleftRight hrightLeft

end SemiTransitiveOrientation

namespace AcyclicOrientation

/-- Graph-level form of the string-digraph edge lemma: for every positive `t`, an
acyclic orientation has a `t`-uniform covering word whose alternation graph contains
the original graph. Eliminating the extra edges is the remaining converse task. -/
theorem exists_uniform_superword [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (orientation : AcyclicOrientation G)
    (t : ℕ) (ht : 0 < t) :
    ∃ word : Word V,
      word.IsUniform t ∧ word.Covers ∧ G ≤ alternationGraph word := by
  let listing : TopologicalListing (@stringRel V orientation.rel t) :=
    StringTopologicalListing.ofAcyclic orientation.acyclic
  let word := StringTopologicalListing.erasedWord listing
  refine ⟨word, StringTopologicalListing.erasedWord_uniform listing,
    StringTopologicalListing.erasedWord_covers listing ht, ?_⟩
  intro left right hadj
  rw [alternationGraph_adj]
  rw [← orientation.underlying, SimpleGraph.fromRel_adj] at hadj
  rcases hadj with ⟨hne, hedge | hedge⟩
  · exact StringTopologicalListing.lettersAlternate_of_rel listing hne hedge
  · exact (lettersAlternate_comm word left right).mpr
      (StringTopologicalListing.lettersAlternate_of_rel listing hne.symm hedge)

end AcyclicOrientation

end Lax458700Proofs
