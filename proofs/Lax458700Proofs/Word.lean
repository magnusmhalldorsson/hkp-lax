import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.Chain

/-!
# Words and alternation

These are the foundational definitions for word-representable graphs. A word is a finite
list of letters. Two distinct letters alternate when deleting every other letter leaves a
word with no equal adjacent letters. The alternation graph of a word joins exactly those
pairs, and a graph is word-representable when some word containing every vertex has that
alternation graph.
-/

namespace Lax458700Proofs

universe u

variable {Alphabet : Type u}

/-- A finite word over `Alphabet`. -/
abbrev Word (Alphabet : Type u) := List Alphabet

/-- Delete every letter other than `first` and `second`. -/
def Word.restrictToPair [DecidableEq Alphabet] (word : Word Alphabet)
    (first second : Alphabet) : Word Alphabet :=
  word.filter fun letter ↦ decide (letter = first ∨ letter = second)

theorem Word.restrictToPair_comm [DecidableEq Alphabet] (word : Word Alphabet)
    (first second : Alphabet) :
    word.restrictToPair first second = word.restrictToPair second first := by
  simp [Word.restrictToPair, or_comm]

@[simp]
theorem Word.restrictToPair_append [DecidableEq Alphabet]
    (firstWord secondWord : Word Alphabet) (first second : Alphabet) :
    (firstWord ++ secondWord).restrictToPair first second =
      firstWord.restrictToPair first second ++
        secondWord.restrictToPair first second := by
  simp [Word.restrictToPair]

/-- A list alternates locally when consecutive entries are always different. -/
def IsAlternating (word : List Alphabet) : Prop :=
  word.IsChain (· ≠ ·)

instance [DecidableEq Alphabet] (word : List Alphabet) :
    Decidable (IsAlternating word) := by
  unfold IsAlternating
  infer_instance

/-- Two distinct letters alternate in a word when its restriction to them has no equal
adjacent letters. -/
def LettersAlternate [DecidableEq Alphabet] (word : Word Alphabet)
    (first second : Alphabet) : Prop :=
  first ≠ second ∧ IsAlternating (word.restrictToPair first second)

instance [DecidableEq Alphabet] (word : Word Alphabet) (first second : Alphabet) :
    Decidable (LettersAlternate word first second) := by
  unfold LettersAlternate
  infer_instance

theorem lettersAlternate_comm [DecidableEq Alphabet] (word : Word Alphabet)
    (first second : Alphabet) :
    LettersAlternate word first second ↔ LettersAlternate word second first := by
  rw [LettersAlternate, LettersAlternate, word.restrictToPair_comm first second]
  exact and_congr ne_comm Iff.rfl

/-- If two letters alternate in a concatenation, they alternate in every whole middle
block of that concatenation. -/
theorem LettersAlternate.middle [DecidableEq Alphabet]
    {before middle after : Word Alphabet} {first second : Alphabet}
    (h : LettersAlternate (before ++ middle ++ after) first second) :
    LettersAlternate middle first second := by
  refine ⟨h.1, ?_⟩
  have hchain := h.2
  simp only [Word.restrictToPair_append] at hchain
  exact hchain.infix (List.infix_append
    (before.restrictToPair first second)
    (middle.restrictToPair first second)
    (after.restrictToPair first second))

/-- The graph represented by a word: two vertices are adjacent exactly when their letters
alternate in the word. -/
def alternationGraph [DecidableEq Alphabet] (word : Word Alphabet) :
    SimpleGraph Alphabet :=
  SimpleGraph.fromRel (LettersAlternate word)

@[simp]
theorem alternationGraph_adj [DecidableEq Alphabet] (word : Word Alphabet)
    (first second : Alphabet) :
    (alternationGraph word).Adj first second ↔
      LettersAlternate word first second := by
  change (SimpleGraph.fromRel (LettersAlternate word)).Adj first second ↔
    LettersAlternate word first second
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact (lettersAlternate_comm word first second).mpr h
  · intro h
    exact ⟨h.1, Or.inl h⟩

/-- A word covers its alphabet when every possible letter occurs at least once. -/
def Word.Covers (word : Word Alphabet) : Prop :=
  ∀ letter : Alphabet, letter ∈ word

/-- A word represents `G` when it contains every vertex and its alternating pairs are
exactly the edges of `G`. -/
structure WordRepresentation [DecidableEq Alphabet] (G : SimpleGraph Alphabet) where
  word : Word Alphabet
  covers : word.Covers
  underlying : alternationGraph word = G

/-- A graph is word-representable when it admits a word representation. -/
def IsWordRepresentable [DecidableEq Alphabet] (G : SimpleGraph Alphabet) : Prop :=
  Nonempty (WordRepresentation G)

/-- Every vertex occurs exactly `k` times in a `k`-uniform word. -/
def Word.IsUniform [DecidableEq Alphabet] (k : ℕ) (word : Word Alphabet) : Prop :=
  ∀ letter : Alphabet, word.count letter = k

/-- Concatenating a list of equally uniform words adds their common multiplicities. -/
theorem Word.IsUniform.flatten [DecidableEq Alphabet]
    {words : List (Word Alphabet)} {k : ℕ}
    (hwords : ∀ word ∈ words, word.IsUniform k) :
    Word.IsUniform (words.length * k) words.flatten := by
  intro letter
  induction words with
  | nil => simp
  | cons word words ih =>
      rw [List.flatten_cons, List.count_append, hwords word (by simp)]
      rw [ih (fun next hnext ↦ hwords next (by simp [hnext]))]
      simp [Nat.succ_mul, Nat.add_comm]

/-- A word representation together with a common positive multiplicity for all letters. -/
structure UniformWordRepresentation [DecidableEq Alphabet] (G : SimpleGraph Alphabet) where
  representation : WordRepresentation G
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  uniform : representation.word.IsUniform multiplicity

/-- A graph has a uniform word representation if some positive multiplicity works for all
vertices. -/
def IsUniformlyWordRepresentable [DecidableEq Alphabet]
    (G : SimpleGraph Alphabet) : Prop :=
  Nonempty (UniformWordRepresentation G)

example : IsAlternating ([0, 1, 0, 1] : Word Nat) := by
  decide

example : ¬IsAlternating ([0, 0, 1, 1] : Word Nat) := by
  decide

example : LettersAlternate ([0, 2, 1, 2, 0, 1] : Word Nat) 0 1 := by
  decide

end Lax458700Proofs
