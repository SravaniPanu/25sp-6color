import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic
import Mathlib.Data.Fintype.Card

open SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V)

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

-- Returns neighbors of a vertex as a Finset
local instance : DecidableRel (G.Adj) := by assumption
def neighbors (v : V) : Finset V :=
  Finset.univ.filter (λ u => G.Adj v u)

-- if the degree of every vertex is less than n, then you can find a proper coloring for the entire graph
theorem coloring_of_bounded_degree
  {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (n : ℕ)
  (h_deg : ∀ v : V, G.degree v < n)
  (h_pos : 0 < n) :
  Nonempty (G.Coloring (Fin n)) := by

  induction' card_V : Fintype.card V using Nat.strong_induction_on with k ih generalizing V

  cases k with
  | zero =>
    have h_empty : IsEmpty V := Fintype.card_eq_zero_iff.mp card_V
    use fun x => IsEmpty.elim h_empty x
    intro u v h_adj
    exact IsEmpty.elim h_empty u
  | succ k' =>
    haveI : Nonempty V := Fintype.card_pos_iff.mp (by rw [card_V]; exact Nat.succ_pos _)
    obtain ⟨v⟩ := ‹Nonempty V›

    let V' := {u : V // u ≠ v}
    let G' : SimpleGraph {u : V // u ≠ v} := SimpleGraph.induce (fun u => u ≠ v) G

    have card_V' : Fintype.card V' < Fintype.card V := by
      -- apply Fintype.card_subtype_lt (p := fun u => u ≠ v)
      sorry

    have deg' : ∀ u : V', G'.degree u < n := by
      sorry
    sorry
