import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Count

/-!
---
title: Word representations of graphs
type: definition
---
A word represents a graph when it contains every vertex and two distinct vertices
are adjacent exactly when their letters alternate after all other letters are deleted.
A positive $k$-uniform representation contains every vertex exactly $k$ times.
-/

namespace Lax458700.Words

universe u
variable {V : Type u} [DecidableEq V]

/-- Restrict a word to two specified letters. -/
def restrictToPair (word : List V) (x y : V) : List V :=
  word.filter fun letter ↦ decide (letter = x ∨ letter = y)

/-- Alternation means that consecutive letters in the two-letter restriction differ. -/
def LettersAlternate (word : List V) (x y : V) : Prop :=
  x ≠ y ∧ (restrictToPair word x y).IsChain (· ≠ ·)

/-- A representing word includes every vertex and realizes exactly the graph's edges. -/
def Represents (G : SimpleGraph V) (word : List V) : Prop :=
  (∀ vertex : V, vertex ∈ word) ∧
    ∀ x y : V, G.Adj x y ↔ LettersAlternate word x y

def IsWordRepresentable (G : SimpleGraph V) : Prop :=
  ∃ word : List V, Represents G word

/-- This definition excludes zero multiplicity, including for the empty graph. -/
def HasUniformRepresentation (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ word : List V, Represents G word ∧ 0 < k ∧
    ∀ vertex : V, word.count vertex = k

end Lax458700.Words
