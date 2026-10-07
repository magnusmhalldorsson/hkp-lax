import Lax458700Proofs.WordOrientation
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.List.Count

/-!
# Uniform words and occurrence interleaving

This module develops the occurrence-position lemmas used to prove that the
first-occurrence orientation of a uniform representing word is semi-transitive.
-/

namespace Lax458700Proofs

universe u

variable {V : Type u} [DecidableEq V]

omit [DecidableEq V] in
/-- Finding the `n`th `q`-element after filtering by `p` is the same as finding the
corresponding `p ∧ q` element in the original list. -/
theorem List.findIdxNth_filter_comp (word : List V) (p q : V → Bool) (n : ℕ) :
    word.findIdxNth (fun letter ↦ p letter && q letter) n =
      word.findIdxNth p ((word.filter p).findIdxNth q n) := by
  induction word generalizing n with
  | nil => simp
  | cons letter word ih =>
      by_cases hp : p letter
      · cases hq : q letter <;> cases n <;>
          simp [List.findIdxNth_cons, hp, hq, ih]
      · simp [List.findIdxNth_cons_of_neg, hp, ih]

/-- An `n`th occurrence lies before position `i` exactly when more than `n`
occurrences lie in the prefix ending at `i`. -/
theorem List.idxOfNth_lt_iff_lt_countBefore (word : List V) (letter : V)
    {n i : ℕ} (hi : i ≤ word.length) :
    word.idxOfNth letter n < i ↔ n < word.countBefore letter i := by
  induction word generalizing n i with
  | nil =>
      have hi0 : i = 0 := by simpa using hi
      subst i
      simp
  | cons head tail ih =>
      cases i with
      | zero => simp
      | succ i =>
          have hiTail : i ≤ tail.length := by simpa using hi
          by_cases h : head = letter
          · subst head
            cases n with
            | zero => simp
            | succ n =>
                simpa [List.idxOfNth_cons, List.countBefore_cons] using
                  (ih (n := n) (i := i) hiTail)
          · cases n with
            | zero =>
                simpa [List.idxOfNth_cons, List.countBefore_cons, h] using
                  (ih (n := 0) (i := i) hiTail)
            | succ n =>
                simpa [List.idxOfNth_cons, List.countBefore_cons, h] using
                  (ih (n := n + 1) (i := i) hiTail)

/-- The two-letter word `left right left right ...` with `k` copies of each letter. -/
def alternatingPairs (left right : V) : ℕ → Word V
  | 0 => []
  | k + 1 => left :: right :: alternatingPairs left right k

omit [DecidableEq V] in
@[simp]
theorem alternatingPairs_zero (left right : V) :
    alternatingPairs left right 0 = [] := rfl

omit [DecidableEq V] in
@[simp]
theorem alternatingPairs_succ (left right : V) (k : ℕ) :
    alternatingPairs left right (k + 1) =
      left :: right :: alternatingPairs left right k := rfl

omit [DecidableEq V] in
@[simp]
theorem alternatingPairs_add (left right : V) (m n : ℕ) :
    alternatingPairs left right m ++ alternatingPairs left right n =
      alternatingPairs left right (m + n) := by
  induction m with
  | zero => simp [alternatingPairs]
  | succ m ih => simp [alternatingPairs, ih, Nat.succ_add]

/-- If every block has the same oriented two-letter pattern, flattening the blocks
concatenates those patterns and preserves alternation across block boundaries. -/
theorem restrictToPair_flatten_eq_alternatingPairs
    (words : List (Word V)) (left right : V) (k : ℕ)
    (hwords : ∀ word ∈ words,
      word.restrictToPair left right = alternatingPairs left right k) :
    Word.restrictToPair words.flatten left right =
      alternatingPairs left right (words.length * k) := by
  induction words with
  | nil => simp [Word.restrictToPair]
  | cons word words ih =>
      rw [List.flatten_cons, Word.restrictToPair_append,
        hwords word (by simp), ih (fun next hnext ↦ hwords next (by simp [hnext])),
        alternatingPairs_add]
      congr 1
      simp [Nat.succ_mul, Nat.add_comm]

omit [DecidableEq V] in
@[simp]
theorem length_alternatingPairs (left right : V) (k : ℕ) :
    (alternatingPairs left right k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [alternatingPairs, ih, Nat.mul_succ]

@[simp]
theorem count_left_alternatingPairs {left right : V} (hne : left ≠ right) (k : ℕ) :
    (alternatingPairs left right k).count left = k := by
  induction k with
  | zero => simp [alternatingPairs]
  | succ k ih => simp [alternatingPairs, hne.symm, ih]

@[simp]
theorem count_right_alternatingPairs {left right : V} (hne : left ≠ right) (k : ℕ) :
    (alternatingPairs left right k).count right = k := by
  induction k with
  | zero => simp [alternatingPairs]
  | succ k ih => simp [alternatingPairs, hne, ih]

omit [DecidableEq V] in
theorem isAlternating_alternatingPairs {left right : V} (hne : left ≠ right) (k : ℕ) :
    IsAlternating (alternatingPairs left right k) := by
  induction k with
  | zero => simp [IsAlternating, alternatingPairs]
  | succ k ih =>
      unfold IsAlternating at ih ⊢
      rw [alternatingPairs_succ, List.isChain_cons_cons]
      refine ⟨hne, List.IsChain.cons ih ?_⟩
      cases k with
      | zero => simp [alternatingPairs]
      | succ k => simpa [alternatingPairs] using hne.symm

omit [DecidableEq V] in
theorem getElem_alternatingPairs_even (left right : V) {n k : ℕ} (hn : n < k) :
    (alternatingPairs left right k)[2 * n]'(by simp; omega) = left := by
  induction n generalizing k with
  | zero =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      simp [alternatingPairs]
  | succ n ih =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      change (alternatingPairs left right k)[2 * n]'(by simp; omega) = left
      exact ih (by omega)

omit [DecidableEq V] in
theorem getElem_alternatingPairs_odd (left right : V) {n k : ℕ} (hn : n < k) :
    (alternatingPairs left right k)[2 * n + 1]'(by simp; omega) = right := by
  induction n generalizing k with
  | zero =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      simp [alternatingPairs]
  | succ n ih =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      change (alternatingPairs left right k)[2 * n + 1]'(by simp; omega) = right
      exact ih (by omega)

theorem List.countP_pair_eq_count_add (word : List V) {left right : V}
    (hne : left ≠ right) :
    word.countP (fun letter ↦ decide (letter = left ∨ letter = right)) =
      word.count left + word.count right := by
  induction word with
  | nil => simp
  | cons letter word ih =>
      have hpred :
          (fun item : V ↦ decide (item = left ∨ item = right)) =
            (fun item ↦ decide (item = left) || decide (item = right)) := by
        funext item
        apply Bool.eq_iff_iff.mpr
        simp
      have ih' :
          word.countP (fun item ↦ decide (item = left) || decide (item = right)) =
            word.count left + word.count right := by
        rw [← hpred]
        exact ih
      by_cases hleft : letter = left
      · subst letter
        simp [hne, ih', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · by_cases hright : letter = right
        · subst letter
          simp [hleft, ih', Nat.add_assoc]
        · simp [hleft, hright, ih']

theorem List.countPBefore_pair_eq_countBefore_add (word : List V) {left right : V}
    (hne : left ≠ right) (i : ℕ) :
    word.countPBefore (fun letter ↦ decide (letter = left ∨ letter = right)) i =
      word.countBefore left i + word.countBefore right i := by
  rw [List.countPBefore_eq_countP_take, List.countBefore_eq_count_take,
    List.countBefore_eq_count_take, List.countP_pair_eq_count_add _ hne]

theorem findIdxNth_left_alternatingPairs {left right : V} (hne : left ≠ right)
    {n k : ℕ} (hn : n < k) :
    (alternatingPairs left right k).findIdxNth (· == left) n = 2 * n := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
      cases n with
      | zero => simp [alternatingPairs]
      | succ n =>
          rw [alternatingPairs_succ]
          rw [List.findIdxNth_cons_succ_of_pos (by simp)]
          rw [List.findIdxNth_cons_of_neg (by simp [hne.symm])]
          rw [ih (by omega)]
          omega

theorem findIdxNth_right_alternatingPairs {left right : V} (hne : left ≠ right)
    {n k : ℕ} (hn : n < k) :
    (alternatingPairs left right k).findIdxNth (· == right) n = 2 * n + 1 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
      cases n with
      | zero => simp [alternatingPairs, hne]
      | succ n =>
          rw [alternatingPairs_succ]
          rw [List.findIdxNth_cons_of_neg (by simp [hne])]
          rw [List.findIdxNth_cons_succ_of_pos (by simp)]
          rw [ih (by omega)]
          omega

/-- A two-letter alternating list with equal positive multiplicities is exactly a repetition
of the ordered pair determined by its first letter. -/
theorem eq_alternatingPairs_of_isChain
    {left right : V} (hne : left ≠ right) :
    ∀ (k : ℕ) (letters : List V),
      (∀ letter ∈ letters, letter = left ∨ letter = right) →
      letters.IsChain (· ≠ ·) →
      letters.count left = k + 1 →
      letters.count right = k + 1 →
      letters.head? = some left →
      letters = alternatingPairs left right (k + 1) := by
  intro k
  induction k with
  | zero =>
      intro letters hletters hchain hleft hright hhead
      rcases letters with _ | ⟨first, tail⟩
      · simp at hhead
      · simp only [List.head?_cons, Option.some.injEq] at hhead
        subst first
        rcases tail with _ | ⟨second, rest⟩
        · simp [hne] at hright
        · have hsecond := hletters second (by simp)
          have hneSecond : left ≠ second := (List.isChain_cons_cons.mp hchain).1
          have hsecondEq : second = right := hsecond.resolve_left hneSecond.symm
          subst second
          have hrestLeft : rest.count left = 0 := by
            simpa [hne, hne.symm] using hleft
          have hrestRight : rest.count right = 0 := by
            simpa [hne, hne.symm] using hright
          have hrest : rest = [] := by
            apply List.eq_nil_iff_forall_not_mem.mpr
            intro letter hmem
            rcases hletters letter (by simp [hmem]) with heq | heq
            · have hpos : 0 < rest.count left :=
                List.count_pos_iff.mpr (heq ▸ hmem)
              omega
            · have hpos : 0 < rest.count right :=
                List.count_pos_iff.mpr (heq ▸ hmem)
              omega
          subst rest
          simp [alternatingPairs]
  | succ k ih =>
      intro letters hletters hchain hleft hright hhead
      rcases letters with _ | ⟨first, tail⟩
      · simp at hhead
      · simp only [List.head?_cons, Option.some.injEq] at hhead
        subst first
        rcases tail with _ | ⟨second, rest⟩
        · simp [hne] at hright
        · have hsecond := hletters second (by simp)
          have hneSecond : left ≠ second := (List.isChain_cons_cons.mp hchain).1
          have hsecondEq : second = right := hsecond.resolve_left hneSecond.symm
          subst second
          have hrestLeft : rest.count left = k + 1 := by
            simpa [hne, hne.symm, Nat.add_assoc] using hleft
          have hrestRight : rest.count right = k + 1 := by
            simpa [hne, hne.symm, Nat.add_assoc] using hright
          have hrestNonempty : rest ≠ [] := by
            intro h
            subst rest
            simp at hrestLeft
          have hrestHead : rest.head? = some left := by
            rcases rest with _ | ⟨third, rest'⟩
            · exact (hrestNonempty rfl).elim
            · have hthird := hletters third (by simp)
              have hrightNeThird : right ≠ third :=
                (List.isChain_cons_cons.mp hchain.tail).1
              have : third = left := hthird.resolve_right hrightNeThird.symm
              simp [this]
          have hrestLetters : ∀ letter ∈ rest, letter = left ∨ letter = right := by
            intro letter hmem
            exact hletters letter (by simp [hmem])
          have hrestChain : rest.IsChain (· ≠ ·) := hchain.tail.tail
          rw [ih rest hrestLetters hrestChain hrestLeft hrestRight hrestHead]
          rfl

namespace Word

theorem count_left_restrictToPair (word : Word V) (left right : V) :
    (word.restrictToPair left right).count left = word.count left := by
  induction word with
  | nil => simp [Word.restrictToPair]
  | cons letter word ih =>
      by_cases h : letter = left
      · subst letter
        simp [Word.restrictToPair]
      · by_cases h' : letter = right
        · subst letter
          simp [Word.restrictToPair, h]
        · simp [Word.restrictToPair, h, h']

theorem count_right_restrictToPair (word : Word V) (left right : V) :
    (word.restrictToPair left right).count right = word.count right := by
  rw [word.restrictToPair_comm left right]
  exact count_left_restrictToPair word right left

/-- If both letters occur and `left` has the earlier first occurrence, then it is the
first letter of the two-letter restriction. -/
theorem head?_restrictToPair_eq_left {word : Word V} {left right : V}
    (hleft : left ∈ word) (hright : right ∈ word)
    (hlt : word.idxOf left < word.idxOf right) :
    (word.restrictToPair left right).head? = some left := by
  induction word with
  | nil => simp at hleft
  | cons letter word ih =>
      by_cases hLetterLeft : letter = left
      · subst letter
        simp [Word.restrictToPair]
      · by_cases hLetterRight : letter = right
        · subst letter
          simp [List.idxOf_cons_ne _ hLetterLeft] at hlt
        · have hleftTail : left ∈ word :=
            (List.mem_cons.mp hleft).resolve_left (fun h ↦ hLetterLeft h.symm)
          have hrightTail : right ∈ word :=
            (List.mem_cons.mp hright).resolve_left (fun h ↦ hLetterRight h.symm)
          have hltTail : word.idxOf left < word.idxOf right := by
            simpa [List.idxOf_cons_ne _ hLetterLeft,
              List.idxOf_cons_ne _ hLetterRight] using hlt
          simpa [Word.restrictToPair, hLetterLeft, hLetterRight] using
            ih hleftTail hrightTail hltTail

end Word

/-- In a uniform word, an alternating pair whose first occurrences are ordered
`left`, then `right`, restricts to the exact pattern `(left right)^k`. -/
theorem restrictToPair_eq_alternatingPairs
    {word : Word V} {left right : V} {k : ℕ}
    (hne : left ≠ right) (hk : 0 < k)
    (hleft : word.count left = k) (hright : word.count right = k)
    (halternate : LettersAlternate word left right)
    (hlt : word.idxOf left < word.idxOf right) :
    word.restrictToPair left right = alternatingPairs left right k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  apply eq_alternatingPairs_of_isChain hne n
  · intro letter hmem
    unfold Word.restrictToPair at hmem
    have hpred := List.of_mem_filter hmem
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using hpred
  · exact halternate.2
  · simpa [word.count_left_restrictToPair left right] using hleft
  · simpa [word.count_right_restrictToPair left right] using hright
  · apply Word.head?_restrictToPair_eq_left
    · exact List.count_pos_iff.mp (hleft ▸ Nat.succ_pos n)
    · exact List.count_pos_iff.mp (hright ▸ Nat.succ_pos n)
    · exact hlt

/-- The occurrence positions of an ordered alternating pair interleave, layer by layer. -/
theorem occurrence_interleaving_of_restrict_eq
    {word : Word V} {left right : V} {k : ℕ}
    (hne : left ≠ right)
    (hpattern : word.restrictToPair left right = alternatingPairs left right k) :
    ∀ n, n < k →
      word.idxOfNth left n < word.idxOfNth right n ∧
        (n + 1 < k → word.idxOfNth right n < word.idxOfNth left (n + 1)) := by
  let pair : V → Bool := fun letter ↦ decide (letter = left ∨ letter = right)
  change word.filter pair = alternatingPairs left right k at hpattern
  have hpairCount : word.countP pair = 2 * k := by
    rw [List.countP_eq_length_filter, hpattern, length_alternatingPairs]
  have hleftPos : ∀ {n}, n < k →
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
        rw [hpattern, findIdxNth_left_alternatingPairs hne hn]
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
        rw [hpattern, findIdxNth_right_alternatingPairs hne hn]
  intro n hn
  constructor
  · rw [hleftPos hn, hrightPos hn]
    apply List.findIdxNth_lt_findIdxNth_iff.mpr
    constructor <;> omega
  · intro hsucc
    rw [hrightPos hn, hleftPos hsucc]
    apply List.findIdxNth_lt_findIdxNth_iff.mpr
    constructor <;> omega

/-- Conversely, complete layer-by-layer interleaving of two equally frequent letters
forces their two-letter restriction to be the exact repeated-pair pattern. -/
theorem restrictToPair_eq_alternatingPairs_of_occurrence_interleaving
    {word : Word V} {left right : V} {k : ℕ}
    (hne : left ≠ right)
    (hleft : word.count left = k) (hright : word.count right = k)
    (hsame : ∀ n, n < k → word.idxOfNth left n < word.idxOfNth right n)
    (hnext : ∀ n, n + 1 < k → word.idxOfNth right n < word.idxOfNth left (n + 1)) :
    word.restrictToPair left right = alternatingPairs left right k := by
  let pair : V → Bool := fun letter ↦ decide (letter = left ∨ letter = right)
  change word.filter pair = alternatingPairs left right k
  have hfilterLength : (word.filter pair).length = 2 * k := by
    rw [← List.countP_eq_length_filter, List.countP_pair_eq_count_add word hne,
      hleft, hright]
    omega
  apply List.ext_getElem (by simpa using hfilterLength)
  intro i hiFilter hiPairs
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' i
  · have hn : n < k := by
      rw [hfilterLength] at hiFilter
      omega
    have hleftLength : word.idxOfNth left n < word.length :=
      List.idxOfNth_lt_length_of_lt_count (hleft ▸ hn)
    have hrightLength : word.idxOfNth right n < word.length :=
      List.idxOfNth_lt_length_of_lt_count (hright ▸ hn)
    have hrightBefore :
        word.countBefore right (word.idxOfNth left n) = n := by
      have hnotAbove :
          ¬n < word.countBefore right (word.idxOfNth left n) := by
        rw [← List.idxOfNth_lt_iff_lt_countBefore word right
          (Nat.le_of_lt hleftLength)]
        exact Nat.not_lt_of_ge (Nat.le_of_lt (hsame n hn))
      by_cases hn0 : n = 0
      · omega
      · have hnPred : n - 1 < k := by omega
        have hbelow :
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
    rw [getElem_alternatingPairs_even left right hn]
    rw [List.getElem_filter_eq_getElem_getElem_findIdxs hiFilter]
    simp only [List.getElem_findIdxs_eq_findIdxNth, hfind]
    exact List.getElem_idxOfNth_eq
  · have hn : n < k := by
      rw [hfilterLength] at hiFilter
      omega
    have hleftLength : word.idxOfNth left n < word.length :=
      List.idxOfNth_lt_length_of_lt_count (hleft ▸ hn)
    have hrightLength : word.idxOfNth right n < word.length :=
      List.idxOfNth_lt_length_of_lt_count (hright ▸ hn)
    have hleftBefore :
        word.countBefore left (word.idxOfNth right n) = n + 1 := by
      have hbelow :
          n < word.countBefore left (word.idxOfNth right n) := by
        rw [← List.idxOfNth_lt_iff_lt_countBefore word left
          (Nat.le_of_lt hrightLength)]
        exact hsame n hn
      by_cases hlast : n + 1 = k
      · have hbound := List.countBefore_le_count
            (xs := word) (x := left) (i := word.idxOfNth right n)
        omega
      · have hsucc : n + 1 < k := by omega
        have hnotAbove :
            ¬n + 1 < word.countBefore left (word.idxOfNth right n) := by
          rw [← List.idxOfNth_lt_iff_lt_countBefore word left
            (Nat.le_of_lt hrightLength)]
          exact Nat.not_lt_of_ge (Nat.le_of_lt (hnext n hsucc))
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
    rw [getElem_alternatingPairs_odd left right hn]
    rw [List.getElem_filter_eq_getElem_getElem_findIdxs hiFilter]
    simp only [List.getElem_findIdxs_eq_findIdxNth, hfind]
    exact List.getElem_idxOfNth_eq

/-- At each occurrence layer, `left` appears before `right`. -/
def OccurrencePrecedes (word : Word V) (k : ℕ) (left right : V) : Prop :=
  ∀ n, n < k → word.idxOfNth left n < word.idxOfNth right n

theorem occurrencePrecedes_trans (word : Word V) (k : ℕ) {left middle right : V}
    (hlm : OccurrencePrecedes word k left middle)
    (hmr : OccurrencePrecedes word k middle right) :
    OccurrencePrecedes word k left right := by
  intro n hn
  exact (hlm n hn).trans (hmr n hn)

namespace UniformWordRepresentation

/-- Every directed edge in the first-occurrence orientation has interleaving occurrences:
the source precedes the target in each layer, and the target precedes the source in the
next layer. -/
theorem edge_occurrence_interleaving {G : SimpleGraph V}
    (uniformRep : UniformWordRepresentation G) {left right : V}
    (hedge : uniformRep.representation.firstOccurrenceRel left right) :
    OccurrencePrecedes uniformRep.representation.word uniformRep.multiplicity left right ∧
      ∀ n, n + 1 < uniformRep.multiplicity →
        uniformRep.representation.word.idxOfNth right n <
          uniformRep.representation.word.idxOfNth left (n + 1) := by
  let representation := uniformRep.representation
  let word := representation.word
  have hne : left ≠ right := fun h ↦ by
    subst right
    exact Nat.lt_irrefl _ hedge.2
  have halternate : LettersAlternate word left right := by
    rw [← alternationGraph_adj, representation.underlying]
    exact hedge.1
  have hpattern : word.restrictToPair left right =
      alternatingPairs left right uniformRep.multiplicity :=
    restrictToPair_eq_alternatingPairs hne uniformRep.multiplicity_pos
      (uniformRep.uniform left) (uniformRep.uniform right) halternate hedge.2
  have hinterleaves := occurrence_interleaving_of_restrict_eq hne hpattern
  constructor
  · intro n hn
    exact (hinterleaves n hn).1
  · intro n hn
    exact (hinterleaves n (by omega)).2 hn

/-- Occurrence precedence propagates from the consecutive edges of a directed path to
every earlier/later pair of vertices on that path. -/
theorem path_pairwise_occurrencePrecedes {G : SimpleGraph V}
    (uniformRep : UniformWordRepresentation G)
    (path : DirectedPath uniformRep.representation.firstOccurrenceRel) :
    path.vertices.Pairwise
      (OccurrencePrecedes uniformRep.representation.word uniformRep.multiplicity) := by
  let word := uniformRep.representation.word
  let k := uniformRep.multiplicity
  let before : V → V → Prop := OccurrencePrecedes word k
  have hchain : path.vertices.IsChain before :=
    path.follows.imp fun {_ _} hedge ↦
      (uniformRep.edge_occurrence_interleaving hedge).1
  let _ : Trans before before before :=
    ⟨fun {_ _ _} hlm hmr ↦ occurrencePrecedes_trans word k hlm hmr⟩
  exact hchain.pairwise

/-- A shortcut edge in the first-occurrence orientation closes its entire directed path. -/
theorem firstOccurrence_path_isTransitivelyClosed {G : SimpleGraph V}
    (uniformRep : UniformWordRepresentation G)
    (path : DirectedPath uniformRep.representation.firstOccurrenceRel)
    (hshortcut : uniformRep.representation.firstOccurrenceRel path.start path.finish) :
    path.IsTransitivelyClosed := by
  let representation := uniformRep.representation
  let word := representation.word
  let k := uniformRep.multiplicity
  have hlengthPos : 0 < path.vertices.length :=
    List.length_pos_iff.mpr path.nonempty
  have hstart : path.start = path.vertices[0]'hlengthPos := by
    exact List.head_eq_getElem_zero path.nonempty
  have hfinish : path.finish =
      path.vertices[path.vertices.length - 1]'(by omega) := by
    exact List.getLast_eq_getElem path.nonempty
  have hpathBefore := uniformRep.path_pairwise_occurrencePrecedes path
  have hend := uniformRep.edge_occurrence_interleaving hshortcut
  unfold DirectedPath.IsTransitivelyClosed
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  let left := path.vertices[i]
  let right := path.vertices[j]
  have hsame : OccurrencePrecedes word k left right :=
    (List.pairwise_iff_getElem.mp hpathBefore) i j hi hj hij
  have hnext : ∀ n, n + 1 < k →
      word.idxOfNth right n < word.idxOfNth left (n + 1) := by
    intro n hn
    have hrightFinish :
        word.idxOfNth right n ≤ word.idxOfNth path.finish n := by
      by_cases hjLast : j = path.vertices.length - 1
      · subst j
        simp [right, word, hfinish]
      · have hjBeforeLast : j < path.vertices.length - 1 := by omega
        have hbefore := (List.pairwise_iff_getElem.mp hpathBefore) j
          (path.vertices.length - 1) hj (by omega) hjBeforeLast
        simpa [right, word, hfinish] using
          Nat.le_of_lt (hbefore n (by omega))
    have hstartLeft :
        word.idxOfNth path.start (n + 1) ≤ word.idxOfNth left (n + 1) := by
      by_cases hiZero : i = 0
      · subst i
        simp [left, word, hstart]
      · have hzeroBefore : 0 < i := Nat.pos_of_ne_zero hiZero
        have hbefore := (List.pairwise_iff_getElem.mp hpathBefore) 0 i
          hlengthPos hi hzeroBefore
        simpa [left, word, hstart] using
          Nat.le_of_lt (hbefore (n + 1) hn)
    exact lt_of_le_of_lt hrightFinish
      (lt_of_lt_of_le (hend.2 n hn) hstartLeft)
  have hne : left ≠ right := by
    intro heq
    have hlt := hsame 0 uniformRep.multiplicity_pos
    have : word.idxOfNth left 0 < word.idxOfNth left 0 := by
      simp [heq] at hlt
    exact Nat.lt_irrefl _ this
  have hpattern : word.restrictToPair left right = alternatingPairs left right k :=
    restrictToPair_eq_alternatingPairs_of_occurrence_interleaving hne
      (uniformRep.uniform left) (uniformRep.uniform right) hsame hnext
  have halternate : LettersAlternate word left right := by
    refine ⟨hne, ?_⟩
    rw [hpattern]
    exact isAlternating_alternatingPairs hne k
  have hadj : G.Adj left right := by
    rw [← representation.underlying, alternationGraph_adj]
    exact halternate
  have hfirst : word.idxOf left < word.idxOf right := by
    simpa only [List.idxOfNth_zero] using
      hsame 0 uniformRep.multiplicity_pos
  exact ⟨hadj, hfirst⟩

/-- The first-occurrence orientation of a uniform word representation is semi-transitive. -/
def toSemiTransitiveOrientation {G : SimpleGraph V}
    (uniformRep : UniformWordRepresentation G) : SemiTransitiveOrientation G :=
  uniformRep.representation.firstOccurrenceSemiTransitiveOrientation
    (fun path _ hshortcut ↦
      uniformRep.firstOccurrence_path_isTransitivelyClosed path hshortcut)

/-- Every uniformly word-representable graph is semi-transitively orientable. -/
theorem isSemiTransitivelyOrientable {G : SimpleGraph V}
    (uniformRep : UniformWordRepresentation G) : IsSemiTransitivelyOrientable G :=
  ⟨uniformRep.toSemiTransitiveOrientation⟩

end UniformWordRepresentation

/-- Existential form of the uniform-word forward theorem. -/
theorem IsUniformlyWordRepresentable.isSemiTransitivelyOrientable {G : SimpleGraph V}
    (hG : IsUniformlyWordRepresentable G) : IsSemiTransitivelyOrientable G := by
  rcases hG with ⟨uniformRep⟩
  exact uniformRep.isSemiTransitivelyOrientable

end Lax458700Proofs
