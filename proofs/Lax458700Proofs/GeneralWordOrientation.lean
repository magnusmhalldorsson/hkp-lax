import Lax458700Proofs.UniformWordOrientation

/-!
# The forward theorem for arbitrary representing words

The first-occurrence orientation is semi-transitive without a uniformity assumption.
Along an oriented alternating edge, occurrence counts never increase and drop by at most
one. On a shortcut path this forces every earlier/later pair to have compatible counts;
the corresponding occurrence positions then interleave.
-/

namespace Lax458700Proofs

universe u

variable {V : Type u} [DecidableEq V]

/-- The alternating word with one more `left` than `right`. -/
def alternatingPairsThenLeft (left right : V) : ℕ → Word V
  | 0 => [left]
  | k + 1 => left :: right :: alternatingPairsThenLeft left right k

omit [DecidableEq V] in
@[simp]
theorem alternatingPairsThenLeft_zero (left right : V) :
    alternatingPairsThenLeft left right 0 = [left] := rfl

omit [DecidableEq V] in
@[simp]
theorem alternatingPairsThenLeft_succ (left right : V) (k : ℕ) :
    alternatingPairsThenLeft left right (k + 1) =
      left :: right :: alternatingPairsThenLeft left right k := rfl

omit [DecidableEq V] in
@[simp]
theorem head?_alternatingPairsThenLeft (left right : V) (k : ℕ) :
    (alternatingPairsThenLeft left right k).head? = some left := by
  cases k <;> rfl

omit [DecidableEq V] in
@[simp]
theorem length_alternatingPairsThenLeft (left right : V) (k : ℕ) :
    (alternatingPairsThenLeft left right k).length = 2 * k + 1 := by
  induction k with
  | zero => simp [alternatingPairsThenLeft]
  | succ k ih => simp [alternatingPairsThenLeft, ih, Nat.mul_succ]

@[simp]
theorem count_left_alternatingPairsThenLeft {left right : V}
    (hne : left ≠ right) (k : ℕ) :
    (alternatingPairsThenLeft left right k).count left = k + 1 := by
  induction k with
  | zero => simp [alternatingPairsThenLeft]
  | succ k ih => simp [alternatingPairsThenLeft, hne.symm, ih]

@[simp]
theorem count_right_alternatingPairsThenLeft {left right : V}
    (hne : left ≠ right) (k : ℕ) :
    (alternatingPairsThenLeft left right k).count right = k := by
  induction k with
  | zero => simp [alternatingPairsThenLeft, hne]
  | succ k ih => simp [alternatingPairsThenLeft, hne, ih]

omit [DecidableEq V] in
theorem isAlternating_alternatingPairsThenLeft {left right : V}
    (hne : left ≠ right) (k : ℕ) :
    IsAlternating (alternatingPairsThenLeft left right k) := by
  induction k with
  | zero => simp [IsAlternating, alternatingPairsThenLeft]
  | succ k ih =>
      unfold IsAlternating at ih ⊢
      rw [alternatingPairsThenLeft_succ, List.isChain_cons_cons]
      refine ⟨hne, List.IsChain.cons ih ?_⟩
      intro next hnext
      rw [head?_alternatingPairsThenLeft] at hnext
      change some left = some next at hnext
      exact (Option.some.inj hnext) ▸ hne.symm

omit [DecidableEq V] in
theorem getElem_alternatingPairsThenLeft_even (left right : V)
    {n k : ℕ} (hn : n < k + 1) :
    (alternatingPairsThenLeft left right k)[2 * n]'(by simp; omega) = left := by
  induction n generalizing k with
  | zero => cases k <;> simp [alternatingPairsThenLeft]
  | succ n ih =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      change (alternatingPairsThenLeft left right k)[2 * n]'(by simp; omega) = left
      exact ih (by omega)

omit [DecidableEq V] in
theorem getElem_alternatingPairsThenLeft_odd (left right : V)
    {n k : ℕ} (hn : n < k) :
    (alternatingPairsThenLeft left right k)[2 * n + 1]'(by simp; omega) = right := by
  induction n generalizing k with
  | zero =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      simp [alternatingPairsThenLeft]
  | succ n ih =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      change (alternatingPairsThenLeft left right k)[2 * n + 1]'(by simp; omega) = right
      exact ih (by omega)

theorem findIdxNth_left_alternatingPairsThenLeft {left right : V}
    (hne : left ≠ right) {n k : ℕ} (hn : n < k + 1) :
    (alternatingPairsThenLeft left right k).findIdxNth (· == left) n = 2 * n := by
  induction k generalizing n with
  | zero =>
      have : n = 0 := by omega
      subst n
      simp [alternatingPairsThenLeft]
  | succ k ih =>
      cases n with
      | zero => simp [alternatingPairsThenLeft]
      | succ n =>
          rw [alternatingPairsThenLeft_succ]
          rw [List.findIdxNth_cons_succ_of_pos (by simp)]
          rw [List.findIdxNth_cons_of_neg (by simp [hne.symm])]
          rw [ih (by omega)]
          omega

theorem findIdxNth_right_alternatingPairsThenLeft {left right : V}
    (hne : left ≠ right) {n k : ℕ} (hn : n < k) :
    (alternatingPairsThenLeft left right k).findIdxNth (· == right) n =
      2 * n + 1 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
      cases n with
      | zero => simp [alternatingPairsThenLeft, hne]
      | succ n =>
          rw [alternatingPairsThenLeft_succ]
          rw [List.findIdxNth_cons_of_neg (by simp [hne])]
          rw [List.findIdxNth_cons_succ_of_pos (by simp)]
          rw [ih (by omega)]
          omega

/-- Occurrences in the unequal alternating pattern interleave through the final `left`. -/
theorem occurrence_interleaving_of_restrict_eq_thenLeft
    {word : Word V} {left right : V} {k : ℕ}
    (hne : left ≠ right)
    (hpattern : word.restrictToPair left right =
      alternatingPairsThenLeft left right k) :
    ∀ n, n < k →
      word.idxOfNth left n < word.idxOfNth right n ∧
        word.idxOfNth right n < word.idxOfNth left (n + 1) := by
  let pair : V → Bool := fun letter ↦ decide (letter = left ∨ letter = right)
  change word.filter pair = alternatingPairsThenLeft left right k at hpattern
  have hpairCount : word.countP pair = 2 * k + 1 := by
    rw [List.countP_eq_length_filter, hpattern, length_alternatingPairsThenLeft]
  have hleftPos : ∀ {n}, n < k + 1 →
      word.idxOfNth left n = word.findIdxNth pair (2 * n) := by
    intro n hn
    unfold List.idxOfNth
    calc
      word.findIdxNth (· == left) n =
          word.findIdxNth (fun letter ↦ pair letter && letter == left) n := by
        congr 1
        funext letter
        by_cases h : letter = left <;> simp [pair, h]
      _ = word.findIdxNth pair ((word.filter pair).findIdxNth (· == left) n) :=
        List.findIdxNth_filter_comp word pair (· == left) n
      _ = word.findIdxNth pair (2 * n) := by
        rw [hpattern, findIdxNth_left_alternatingPairsThenLeft hne hn]
  have hrightPos : ∀ {n}, n < k →
      word.idxOfNth right n = word.findIdxNth pair (2 * n + 1) := by
    intro n hn
    unfold List.idxOfNth
    calc
      word.findIdxNth (· == right) n =
          word.findIdxNth (fun letter ↦ pair letter && letter == right) n := by
        congr 1
        funext letter
        by_cases h : letter = right <;> simp [pair, h]
      _ = word.findIdxNth pair ((word.filter pair).findIdxNth (· == right) n) :=
        List.findIdxNth_filter_comp word pair (· == right) n
      _ = word.findIdxNth pair (2 * n + 1) := by
        rw [hpattern, findIdxNth_right_alternatingPairsThenLeft hne hn]
  intro n hn
  constructor
  · rw [hleftPos (by omega), hrightPos hn]
    apply List.findIdxNth_lt_findIdxNth_iff.mpr
    constructor <;> omega
  · rw [hrightPos hn, hleftPos (by omega)]
    apply List.findIdxNth_lt_findIdxNth_iff.mpr
    constructor <;> omega

/-- Complete occurrence interleaving with one additional `left` occurrence reconstructs
the unequal alternating pattern. -/
theorem restrictToPair_eq_alternatingPairsThenLeft_of_occurrence_interleaving
    {word : Word V} {left right : V} {k : ℕ}
    (hne : left ≠ right)
    (hleft : word.count left = k + 1) (hright : word.count right = k)
    (hsame : ∀ n, n < k → word.idxOfNth left n < word.idxOfNth right n)
    (hnext : ∀ n, n < k → word.idxOfNth right n < word.idxOfNth left (n + 1)) :
    word.restrictToPair left right = alternatingPairsThenLeft left right k := by
  let pair : V → Bool := fun letter ↦ decide (letter = left ∨ letter = right)
  change word.filter pair = alternatingPairsThenLeft left right k
  have hfilterLength : (word.filter pair).length = 2 * k + 1 := by
    rw [← List.countP_eq_length_filter, List.countP_pair_eq_count_add word hne,
      hleft, hright]
    omega
  apply List.ext_getElem (by simpa using hfilterLength)
  intro i hiFilter hiPattern
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' i
  · have hn : n < k + 1 := by
      rw [hfilterLength] at hiFilter
      omega
    have hleftLength : word.idxOfNth left n < word.length :=
      List.idxOfNth_lt_length_of_lt_count (hleft ▸ hn)
    have hrightBefore :
        word.countBefore right (word.idxOfNth left n) = n := by
      have hnotAbove :
          ¬n < word.countBefore right (word.idxOfNth left n) := by
        by_cases hnLast : n = k
        · have hbound := List.countBefore_le_count
              (xs := word) (x := right) (i := word.idxOfNth left n)
          omega
        · rw [← List.idxOfNth_lt_iff_lt_countBefore word right
            (Nat.le_of_lt hleftLength)]
          exact Nat.not_lt_of_ge (Nat.le_of_lt (hsame n (by omega)))
      by_cases hn0 : n = 0
      · omega
      · have hbelow :
            n - 1 < word.countBefore right (word.idxOfNth left n) := by
          rw [← List.idxOfNth_lt_iff_lt_countBefore word right
            (Nat.le_of_lt hleftLength)]
          simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)] using
            hnext (n - 1) (by omega)
        omega
    have hrank :
        word.countPBefore pair (word.idxOfNth left n) = 2 * n := by
      rw [List.countPBefore_pair_eq_countBefore_add word hne,
        List.countBefore_idxOfNth_of_lt_count (hleft ▸ hn), hrightBefore]
      omega
    have hpresent : pair word[word.idxOfNth left n] = true := by
      rw [List.getElem_idxOfNth_eq]
      simp [pair]
    have hfind : word.findIdxNth pair (2 * n) = word.idxOfNth left n := by
      rw [← hrank]
      exact List.findIdxNth_countPBefore_of_lt_length_of_pos hpresent
    rw [getElem_alternatingPairsThenLeft_even left right hn]
    rw [List.getElem_filter_eq_getElem_getElem_findIdxs hiFilter]
    simp only [List.getElem_findIdxs_eq_findIdxNth, hfind]
    exact List.getElem_idxOfNth_eq
  · have hn : n < k := by
      rw [hfilterLength] at hiFilter
      omega
    have hrightLength : word.idxOfNth right n < word.length :=
      List.idxOfNth_lt_length_of_lt_count (hright ▸ hn)
    have hleftBefore :
        word.countBefore left (word.idxOfNth right n) = n + 1 := by
      have hbelow :
          n < word.countBefore left (word.idxOfNth right n) := by
        rw [← List.idxOfNth_lt_iff_lt_countBefore word left
          (Nat.le_of_lt hrightLength)]
        exact hsame n hn
      have hnotAbove :
          ¬n + 1 < word.countBefore left (word.idxOfNth right n) := by
        rw [← List.idxOfNth_lt_iff_lt_countBefore word left
          (Nat.le_of_lt hrightLength)]
        exact Nat.not_lt_of_ge (Nat.le_of_lt (hnext n hn))
      omega
    have hrank :
        word.countPBefore pair (word.idxOfNth right n) = 2 * n + 1 := by
      rw [List.countPBefore_pair_eq_countBefore_add word hne, hleftBefore,
        List.countBefore_idxOfNth_of_lt_count (hright ▸ hn)]
      omega
    have hpresent : pair word[word.idxOfNth right n] = true := by
      rw [List.getElem_idxOfNth_eq]
      simp [pair]
    have hfind : word.findIdxNth pair (2 * n + 1) = word.idxOfNth right n := by
      rw [← hrank]
      exact List.findIdxNth_countPBefore_of_lt_length_of_pos hpresent
    rw [getElem_alternatingPairsThenLeft_odd left right hn]
    rw [List.getElem_filter_eq_getElem_getElem_findIdxs hiFilter]
    simp only [List.getElem_findIdxs_eq_findIdxNth, hfind]
    exact List.getElem_idxOfNth_eq
omit [DecidableEq V] in
/-- A two-letter alternating list starting in `left` has one of the only two possible
shapes: equal counts, or one final extra `left`. -/
theorem eq_alternatingPattern_of_isChain {left right : V} (_hne : left ≠ right) :
    ∀ letters : List V,
      (∀ letter ∈ letters, letter = left ∨ letter = right) →
      letters.IsChain (· ≠ ·) →
      letters.head? = some left →
      ∃ k, letters = alternatingPairs left right k ∨
        letters = alternatingPairsThenLeft left right k := by
  intro letters
  induction letters using List.twoStepInduction with
  | nil => intro _ _ hhead; simp at hhead
  | singleton first =>
      intro hletters hchain hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst first
      exact ⟨0, Or.inr rfl⟩
  | cons_cons first second rest ihRest _ =>
      intro hletters hchain hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst first
      have hsecond := hletters second (by simp)
      have hneSecond : left ≠ second := (List.isChain_cons_cons.mp hchain).1
      have hsecondEq : second = right := hsecond.resolve_left hneSecond.symm
      subst second
      cases rest with
      | nil => exact ⟨1, Or.inl rfl⟩
      | cons third rest =>
          have hthird := hletters third (by simp)
          have hneThird : right ≠ third :=
            (List.isChain_cons_cons.mp hchain.tail).1
          have hthirdEq : third = left := hthird.resolve_right hneThird.symm
          subst third
          have hrestLetters : ∀ letter ∈ left :: rest,
              letter = left ∨ letter = right := by
            intro letter hmem
            exact hletters letter (by simp [hmem])
          have hrestChain : (left :: rest).IsChain (· ≠ ·) := hchain.tail.tail
          have hrestHead : (left :: rest).head? = some left := by simp
          rcases ihRest hrestLetters hrestChain hrestHead with ⟨k, hk | hk⟩
          · exact ⟨k + 1, Or.inl (by simp [hk])⟩
          · exact ⟨k + 1, Or.inr (by simp [hk])⟩

/-- At every occurrence shared with `right`, `left` occurs first, and `left` has at
least as many occurrences. -/
def OccurrenceDominates (word : Word V) (left right : V) : Prop :=
  word.count right ≤ word.count left ∧
    ∀ n, n < word.count right →
      word.idxOfNth left n < word.idxOfNth right n

theorem occurrenceDominates_trans (word : Word V) {left middle right : V}
    (hlm : OccurrenceDominates word left middle)
    (hmr : OccurrenceDominates word middle right) :
    OccurrenceDominates word left right := by
  constructor
  · exact hmr.1.trans hlm.1
  · intro n hn
    exact (hlm.2 n (lt_of_lt_of_le hn hmr.1)).trans (hmr.2 n hn)

namespace WordRepresentation

/-- Complete occurrence data carried by a directed edge in the first-occurrence
orientation of an arbitrary representing word. -/
theorem edge_occurrence_data {G : SimpleGraph V}
    (representation : WordRepresentation G) {left right : V}
    (hedge : representation.firstOccurrenceRel left right) :
    representation.word.count right ≤ representation.word.count left ∧
      representation.word.count left ≤ representation.word.count right + 1 ∧
      OccurrenceDominates representation.word left right ∧
      ∀ n, n + 1 < representation.word.count left →
        representation.word.idxOfNth right n <
          representation.word.idxOfNth left (n + 1) := by
  let word := representation.word
  change word.count right ≤ word.count left ∧
    word.count left ≤ word.count right + 1 ∧
    OccurrenceDominates word left right ∧
    ∀ n, n + 1 < word.count left →
      word.idxOfNth right n < word.idxOfNth left (n + 1)
  have hne : left ≠ right := fun h ↦ by
    subst right
    exact Nat.lt_irrefl _ hedge.2
  have halternate : LettersAlternate word left right := by
    rw [← alternationGraph_adj, representation.underlying]
    exact hedge.1
  have hhead : (word.restrictToPair left right).head? = some left :=
    Word.head?_restrictToPair_eq_left (representation.covers left)
      (representation.covers right) hedge.2
  have hletters : ∀ letter ∈ word.restrictToPair left right,
      letter = left ∨ letter = right := by
    intro letter hmem
    unfold Word.restrictToPair at hmem
    have hpred := List.of_mem_filter hmem
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using hpred
  rcases eq_alternatingPattern_of_isChain hne (word.restrictToPair left right)
    hletters halternate.2 hhead with ⟨k, hpattern | hpattern⟩
  · have hleftCount : word.count left = k := by
      rw [← word.count_left_restrictToPair left right, hpattern,
        count_left_alternatingPairs hne]
    have hrightCount : word.count right = k := by
      rw [← word.count_right_restrictToPair left right, hpattern,
        count_right_alternatingPairs hne]
    have hinter := occurrence_interleaving_of_restrict_eq hne hpattern
    refine ⟨by omega, by omega, ⟨by omega, ?_⟩, ?_⟩
    · intro n hn
      exact (hinter n (by omega)).1
    · intro n hn
      exact (hinter n (by omega)).2 (by omega)
  · have hleftCount : word.count left = k + 1 := by
      rw [← word.count_left_restrictToPair left right, hpattern,
        count_left_alternatingPairsThenLeft hne]
    have hrightCount : word.count right = k := by
      rw [← word.count_right_restrictToPair left right, hpattern,
        count_right_alternatingPairsThenLeft hne]
    have hinter := occurrence_interleaving_of_restrict_eq_thenLeft hne hpattern
    refine ⟨by omega, by omega, ⟨by omega, ?_⟩, ?_⟩
    · intro n hn
      exact (hinter n (by omega)).1
    · intro n hn
      exact (hinter n (by omega)).2

/-- Occurrence domination propagates from consecutive edges to every earlier/later pair
on a directed path. -/
theorem path_pairwise_occurrenceDominates {G : SimpleGraph V}
    (representation : WordRepresentation G)
    (path : DirectedPath representation.firstOccurrenceRel) :
    path.vertices.Pairwise (OccurrenceDominates representation.word) := by
  let word := representation.word
  let dominates : V → V → Prop := OccurrenceDominates word
  have hchain : path.vertices.IsChain dominates :=
    path.follows.imp fun {_ _} hedge ↦
      (representation.edge_occurrence_data hedge).2.2.1
  let _ : Trans dominates dominates dominates :=
    ⟨fun {_ _ _} hlm hmr ↦ occurrenceDominates_trans word hlm hmr⟩
  exact hchain.pairwise

/-- The first-occurrence orientation of any representing word closes every shortcut path. -/
theorem firstOccurrence_path_isTransitivelyClosed {G : SimpleGraph V}
    (representation : WordRepresentation G)
    (path : DirectedPath representation.firstOccurrenceRel)
    (hshortcut : representation.firstOccurrenceRel path.start path.finish) :
    path.IsTransitivelyClosed := by
  let word := representation.word
  have hlengthPos : 0 < path.vertices.length :=
    List.length_pos_iff.mpr path.nonempty
  have hstart : path.start = path.vertices[0]'hlengthPos :=
    List.head_eq_getElem_zero path.nonempty
  have hfinish : path.finish =
      path.vertices[path.vertices.length - 1]'(by omega) :=
    List.getLast_eq_getElem path.nonempty
  have hpathDominates := representation.path_pairwise_occurrenceDominates path
  rcases representation.edge_occurrence_data hshortcut with
    ⟨hendCountLower, hendCountUpper, hendDominates, hendNext⟩
  change word.count path.finish ≤ word.count path.start at hendCountLower
  change word.count path.start ≤ word.count path.finish + 1 at hendCountUpper
  change OccurrenceDominates word path.start path.finish at hendDominates
  change ∀ n, n + 1 < word.count path.start →
    word.idxOfNth path.finish n < word.idxOfNth path.start (n + 1) at hendNext
  unfold DirectedPath.IsTransitivelyClosed
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  let left := path.vertices[i]
  let right := path.vertices[j]
  have hdominates : OccurrenceDominates word left right :=
    (List.pairwise_iff_getElem.mp hpathDominates) i j hi hj hij
  have hstartLeft : OccurrenceDominates word path.start left ∨ path.start = left := by
    by_cases hiZero : i = 0
    · right
      subst i
      simpa [left] using hstart
    · left
      have hbefore := (List.pairwise_iff_getElem.mp hpathDominates) 0 i
        hlengthPos hi (Nat.pos_of_ne_zero hiZero)
      simpa [left, word, hstart] using hbefore
  have hrightFinish : OccurrenceDominates word right path.finish ∨ right = path.finish := by
    by_cases hjLast : j = path.vertices.length - 1
    · right
      subst j
      simpa [right] using hfinish.symm
    · left
      have hjBeforeLast : j < path.vertices.length - 1 := by omega
      have hbefore := (List.pairwise_iff_getElem.mp hpathDominates) j
        (path.vertices.length - 1) hj (by omega) hjBeforeLast
      simpa [right, word, hfinish] using hbefore
  have hleftCountStart : word.count left ≤ word.count path.start := by
    rcases hstartLeft with h | h
    · exact h.1
    · simp [h]
  have hfinishCountRight : word.count path.finish ≤ word.count right := by
    rcases hrightFinish with h | h
    · exact h.1
    · simp [h]
  have hcountUpper : word.count left ≤ word.count right + 1 := by
    omega
  have hsame : ∀ n, n < word.count right →
      word.idxOfNth left n < word.idxOfNth right n := hdominates.2
  have hnext : ∀ n, n + 1 < word.count left →
      word.idxOfNth right n < word.idxOfNth left (n + 1) := by
    intro n hn
    have hnFinish : n < word.count path.finish := by
      omega
    have hrightFinishPos :
        word.idxOfNth right n ≤ word.idxOfNth path.finish n := by
      rcases hrightFinish with h | h
      · exact Nat.le_of_lt (h.2 n hnFinish)
      · simp [h]
    have hstartLeftPos :
        word.idxOfNth path.start (n + 1) ≤ word.idxOfNth left (n + 1) := by
      rcases hstartLeft with h | h
      · exact Nat.le_of_lt (h.2 (n + 1) hn)
      · simp [h]
    exact lt_of_le_of_lt hrightFinishPos
      (lt_of_lt_of_le (hendNext n (by omega)) hstartLeftPos)
  have hrightPos : 0 < word.count right :=
    List.count_pos_iff.mpr (representation.covers right)
  have hfirst : word.idxOf left < word.idxOf right := by
    simpa only [List.idxOfNth_zero] using hsame 0 hrightPos
  have hne : left ≠ right := fun h ↦ by
    rw [← h] at hfirst
    exact Nat.lt_irrefl _ hfirst
  have halternate : LettersAlternate word left right := by
    refine ⟨hne, ?_⟩
    rcases Nat.eq_or_lt_of_le hdominates.1 with hcountEq | hcountLt
    · have hpattern := restrictToPair_eq_alternatingPairs_of_occurrence_interleaving
          hne hcountEq.symm rfl hsame (fun n hn ↦ hnext n (by omega))
      rw [hpattern]
      exact isAlternating_alternatingPairs hne (word.count right)
    · have hleftCount : word.count left = word.count right + 1 := by omega
      have hpattern :=
        restrictToPair_eq_alternatingPairsThenLeft_of_occurrence_interleaving
          hne hleftCount rfl hsame (fun n hn ↦ hnext n (by omega))
      rw [hpattern]
      exact isAlternating_alternatingPairsThenLeft hne (word.count right)
  have hadj : G.Adj left right := by
    rw [← representation.underlying, alternationGraph_adj]
    exact halternate
  exact ⟨hadj, hfirst⟩

/-- The first-occurrence orientation of an arbitrary word representation is
semi-transitive. -/
def toSemiTransitiveOrientation {G : SimpleGraph V}
    (representation : WordRepresentation G) : SemiTransitiveOrientation G :=
  representation.firstOccurrenceSemiTransitiveOrientation
    (fun path _ hshortcut ↦
      representation.firstOccurrence_path_isTransitivelyClosed path hshortcut)

/-- Every word representation yields a semi-transitive orientation. -/
theorem isSemiTransitivelyOrientable {G : SimpleGraph V}
    (representation : WordRepresentation G) : IsSemiTransitivelyOrientable G :=
  ⟨representation.toSemiTransitiveOrientation⟩

end WordRepresentation

/-- Full forward direction: every word-representable graph is semi-transitively
orientable. -/
theorem IsWordRepresentable.isSemiTransitivelyOrientable {G : SimpleGraph V}
    (hG : IsWordRepresentable G) : IsSemiTransitivelyOrientable G := by
  rcases hG with ⟨representation⟩
  exact representation.isSemiTransitivelyOrientable

end Lax458700Proofs
