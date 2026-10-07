import Lax458700Proofs.Permutation
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Relation

/-!
# Semi-transitive orientations

This module sets up the orientation side of the characterization of word-representable
graphs. An acyclic orientation is represented by a directed-edge relation whose transitive
closure has no loop. A semi-transitive orientation additionally forbids shortcuts: whenever
a directed path on at least four vertices also has an edge from its first to its last
vertex, every earlier vertex on the path must point to every later vertex.
-/

namespace Lax458700Proofs

universe u

variable {V : Type u}

/-- A vertex-simple directed path for a binary directed-edge relation. -/
structure DirectedPath (rel : V → V → Prop) where
  vertices : List V
  nonempty : vertices ≠ []
  nodup : vertices.Nodup
  follows : vertices.IsChain rel

namespace DirectedPath

/-- The first vertex of a nonempty directed path. -/
def start {rel : V → V → Prop} (path : DirectedPath rel) : V :=
  path.vertices.head path.nonempty

/-- The last vertex of a nonempty directed path. -/
def finish {rel : V → V → Prop} (path : DirectedPath rel) : V :=
  path.vertices.getLast path.nonempty

/-- A path is transitively closed when every earlier vertex points to every later vertex. -/
def IsTransitivelyClosed {rel : V → V → Prop} (path : DirectedPath rel) : Prop :=
  path.vertices.Pairwise rel

/-- A shortcut is a directed path on at least four vertices with a first-to-last edge but
without all the forward edges required by transitivity. -/
def IsShortcut {rel : V → V → Prop} (path : DirectedPath rel) : Prop :=
  4 ≤ path.vertices.length ∧ rel path.start path.finish ∧ ¬path.IsTransitivelyClosed

end DirectedPath

/-- An acyclic orientation of `G`. The relation supplies the directed edges, its transitive
closure is irreflexive, and forgetting directions recovers `G`.

Acyclicity rules out orienting an undirected edge in both directions. -/
structure AcyclicOrientation (G : SimpleGraph V) where
  rel : V → V → Prop
  acyclic : ∀ vertex, ¬Relation.TransGen rel vertex vertex
  underlying : SimpleGraph.fromRel rel = G

namespace AcyclicOrientation

theorem irrefl {G : SimpleGraph V} (orientation : AcyclicOrientation G) (vertex : V) :
    ¬orientation.rel vertex vertex := by
  intro loop
  exact orientation.acyclic vertex (.single loop)

theorem asymm {G : SimpleGraph V} (orientation : AcyclicOrientation G) {u v : V}
    (huv : orientation.rel u v) : ¬orientation.rel v u := by
  intro hvu
  exact orientation.acyclic u (.tail (.single huv) hvu)

theorem rel_implies_adj {G : SimpleGraph V} (orientation : AcyclicOrientation G)
    {u v : V} (huv : orientation.rel u v) : G.Adj u v := by
  rw [← orientation.underlying]
  exact ⟨fun h ↦ orientation.irrefl u (h ▸ huv), Or.inl huv⟩

end AcyclicOrientation

/-- A semi-transitive orientation is an acyclic orientation with no shortcuts. -/
structure SemiTransitiveOrientation (G : SimpleGraph V) extends AcyclicOrientation G where
  complete_of_shortcut :
    ∀ path : DirectedPath rel, 4 ≤ path.vertices.length → rel path.start path.finish →
      path.IsTransitivelyClosed

/-- A graph is semi-transitively orientable if it admits a semi-transitive orientation. -/
def IsSemiTransitivelyOrientable (G : SimpleGraph V) : Prop :=
  Nonempty (SemiTransitiveOrientation G)

namespace SemiTransitiveOrientation

/-- A semi-transitive orientation contains no shortcut. -/
theorem not_isShortcut {G : SimpleGraph V} (orientation : SemiTransitiveOrientation G)
    (path : DirectedPath orientation.rel) : ¬path.IsShortcut := by
  rintro ⟨hlen, hedge, hmissing⟩
  exact hmissing (orientation.complete_of_shortcut path hlen hedge)

/-- A directed path with an edge from its first vertex to its last is transitively
closed. For paths on at least four vertices this is semi-transitivity; the shorter
cases follow directly from the path edges and the endpoint edge. -/
theorem complete_of_endpoint_edge {G : SimpleGraph V}
    (orientation : SemiTransitiveOrientation G)
    (path : DirectedPath orientation.rel)
    (hedge : orientation.rel path.start path.finish) :
    path.IsTransitivelyClosed := by
  by_cases hlen : 4 ≤ path.vertices.length
  · exact orientation.complete_of_shortcut path hlen hedge
  · rcases path with ⟨vertices, hnonempty, hnodup, hfollows⟩
    change vertices.Pairwise orientation.rel
    rcases vertices with _ | ⟨a, tail⟩
    · exact (hnonempty rfl).elim
    · rcases tail with _ | ⟨b, tail⟩
      · simp
      · rcases tail with _ | ⟨c, tail⟩
        · simpa using hfollows
        · rcases tail with _ | ⟨d, tail⟩
          · simp at hfollows ⊢
            simpa [DirectedPath.start, DirectedPath.finish] using
              And.intro (And.intro hfollows.1 hedge) hfollows.2
          · simp at hlen

/-- If an endpoint edge spans three consecutive reachability intervals, then every
vertex at the first junction points to every vertex at the second junction. This is
the reachability form of semi-transitivity used in the string-digraph argument. -/
theorem edge_of_reachable_interval {G : SimpleGraph V}
    (orientation : SemiTransitiveOrientation G)
    {first left right last : V}
    (hbefore : Relation.ReflTransGen orientation.rel first left)
    (hmiddle : Relation.TransGen orientation.rel left right)
    (hafter : Relation.ReflTransGen orientation.rel right last)
    (hshortcut : orientation.rel first last) :
    orientation.rel left right := by
  have hleftRight : left ≠ right := by
    intro heq
    subst right
    exact orientation.acyclic left hmiddle
  rcases List.exists_isChain_cons_of_relationReflTransGen hbefore with
    ⟨before, hbeforeChain, hbeforeLast⟩
  rcases List.exists_isChain_cons_of_relationReflTransGen hmiddle.to_reflTransGen with
    ⟨middle, hmiddleChain, hmiddleLast⟩
  rcases List.exists_isChain_cons_of_relationReflTransGen hafter with
    ⟨after, hafterChain, hafterLast⟩
  have hmiddleNe : middle ≠ [] := by
    intro hempty
    subst middle
    simp at hmiddleLast
    exact hleftRight hmiddleLast
  have hbeforeMiddle : (first :: before ++ middle).IsChain orientation.rel := by
    apply hbeforeChain.append hmiddleChain.tail
    intro a ha b hb
    rcases List.mem_getLast?_eq_getLast ha with ⟨hne, rfl⟩
    rw [hbeforeLast]
    exact hmiddleChain.rel_head? hb
  have hbeforeMiddleLast :
      (first :: before ++ middle).getLast (by simp) = right := by
    rw [List.getLast_append_of_right_ne_nil _ _ hmiddleNe]
    simpa only [List.getLast_cons hmiddleNe] using hmiddleLast
  let vertices := first :: before ++ middle ++ after
  have hverticesChain : vertices.IsChain orientation.rel := by
    apply hbeforeMiddle.append hafterChain.tail
    intro a ha b hb
    rcases List.mem_getLast?_eq_getLast ha with ⟨hne, rfl⟩
    rw [hbeforeMiddleLast]
    exact hafterChain.rel_head? hb
  have hverticesNonempty : vertices ≠ [] := by simp [vertices]
  have hverticesLast : vertices.getLast hverticesNonempty = last := by
    by_cases hafterNe : after = []
    · subst after
      simpa [vertices] using hbeforeMiddleLast.trans hafterLast
    · have hlastAfter : after.getLast hafterNe = last := by
        simpa only [List.getLast_cons hafterNe] using hafterLast
      cases after with
      | nil => exact (hafterNe rfl).elim
      | cons z zs => simpa [vertices] using hlastAfter
  have hverticesNodup : vertices.Nodup := by
    have htransChain : vertices.IsChain (Relation.TransGen orientation.rel) :=
      hverticesChain.imp fun _ _ hedge ↦ .single hedge
    have htransPairwise := htransChain.pairwise
    exact htransPairwise.imp fun hcycle heq ↦ by
      subst heq
      exact orientation.acyclic _ hcycle
  let path : DirectedPath orientation.rel :=
    { vertices := vertices
      nonempty := hverticesNonempty
      nodup := hverticesNodup
      follows := hverticesChain }
  have hpathStart : path.start = first := by
    simp [path, vertices, DirectedPath.start]
  have hpathFinish : path.finish = last := by
    simpa [path, DirectedPath.finish] using hverticesLast
  have hclosed : path.IsTransitivelyClosed :=
    orientation.complete_of_endpoint_edge path (by simpa [hpathStart, hpathFinish])
  have hmiddleSublist : (left :: middle).Sublist vertices := by
    rw [show vertices = (first :: before) ++ middle ++ after by
      simp [vertices, List.append_assoc]]
    have hleftMem : left ∈ first :: before := hbeforeLast ▸ List.getLast_mem _
    have hmiddlePrefix : (left :: middle).Sublist ((first :: before) ++ middle) :=
      (List.singleton_sublist.mpr hleftMem).append (List.Sublist.refl middle)
    exact hmiddlePrefix.trans (List.sublist_append_left _ _)
  have hmiddlePairwise : (left :: middle).Pairwise orientation.rel :=
    hclosed.sublist hmiddleSublist
  apply hmiddlePairwise.rel_head_tail
  have hrightMem : right ∈ left :: middle := hmiddleLast ▸ List.getLast_mem _
  exact (List.mem_cons.mp hrightMem).resolve_left hleftRight.symm

end SemiTransitiveOrientation

/-- Every transitive orientation is semi-transitive: transitivity closes every directed
path, so in particular no shortcut can occur. -/
def TransitiveOrientation.toSemiTransitiveOrientation {G : SimpleGraph V}
    (orientation : TransitiveOrientation G) : SemiTransitiveOrientation G := by
  let _ : IsStrictOrder V orientation.rel := orientation.isStrictOrder
  exact {
    rel := orientation.rel
    acyclic := fun vertex cycle ↦ by
      have hloop : orientation.rel vertex vertex := by
        simpa only [Relation.transGen_eq_self] using cycle
      exact (irrefl_of orientation.rel vertex) hloop
    underlying := orientation.underlying
    complete_of_shortcut := fun path _ _ ↦ path.follows.pairwise
  }

/-- Every comparability graph is semi-transitively orientable. -/
theorem IsComparabilityGraph.isSemiTransitivelyOrientable {G : SimpleGraph V}
    (hG : IsComparabilityGraph G) : IsSemiTransitivelyOrientable G := by
  rcases hG.isTransitivelyOrderable with ⟨orientation⟩
  exact ⟨orientation.toSemiTransitiveOrientation⟩

/-- Every permutation graph is semi-transitively orientable. -/
theorem IsPermutationGraph.isSemiTransitivelyOrientable {G : SimpleGraph V}
    (hG : IsPermutationGraph G) : IsSemiTransitivelyOrientable G :=
  hG.isComparabilityGraph.isSemiTransitivelyOrientable

end Lax458700Proofs
