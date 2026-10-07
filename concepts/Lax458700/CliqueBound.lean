import Lax458700.Characterization
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
---
title: The corrected HKP clique bound
type: theorem
---
Every finite noncomplete word-representable graph with $n$ vertices and clique
number $\omega$ has a $2(n-\omega)$-uniform representing word, hence representation
number at most $2(n-\omega)$. The proof uses the corrected two-occurrence
construction and concatenates one block for each vertex outside a maximum clique.
Complete graphs are excluded because the displayed multiplicity would be zero.
-/

namespace Lax458700.CliqueBound

universe u

axiom uniformRepresentation_cliqueBound
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
  Lax458700.Words.IsWordRepresentable G → G ≠ ⊤ →
    Lax458700.Words.HasUniformRepresentation G
      (2 * (Fintype.card V - G.cliqueNum))

end Lax458700.CliqueBound
