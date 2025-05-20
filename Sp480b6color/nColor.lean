import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V] (G : SimpleGraph V)

-- A coloring with n colors is a map from vertices to Fin n
namespace Coloring

def ColoringType (n : ℕ) := { f : V → Fin n // ∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v }

instance : CoeFun (ColoringType G n) (fun _ => V → Fin n) :=
  ⟨fun f => f.val⟩

end Coloring

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- Returns neighbors of a vertex as a Finset
local instance : DecidableRel (G.Adj) := by assumption
def neighbors (v : V) : Finset V :=
  Finset.univ.filter (λ u => G.Adj v u)

-- Lemma: if a vertex has fewer than n neighbors, and they're all colored, you can extend the coloring
-- working on this
