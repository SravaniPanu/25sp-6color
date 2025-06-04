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

  -- Proof by strong induction on the cardinality of the vertex set V.
  induction' card_V : Fintype.card V using Nat.strong_induction_on with k ih generalizing V

  cases k with
  -- Base case: The vertex set V is empty (cardinality 0).
  | zero =>
    have h_empty : IsEmpty V := Fintype.card_eq_zero_iff.mp card_V
    use (fun x => IsEmpty.elim h_empty x)
    intro u v_node h_adj
    exact IsEmpty.elim h_empty u
  -- Inductive step: Assume the theorem holds for all graphs with fewer than k+1 vertices.
  | succ k' =>
    -- Since k' + 1 > 0, V is not empty, so pick an arbitrary vertex `v`.
    haveI : Nonempty V := Fintype.card_pos_iff.mp (by rw [card_V]; exact Nat.succ_pos _)
    obtain ⟨v⟩ := ‹Nonempty V›

    -- Define V' as the set of all vertices in V except `v`, and G' as the induced subgraph on V'.
    let V' := {u : V // u ≠ v}
    let G' : SimpleGraph {u : V // u ≠ v} := SimpleGraph.induce (fun u => u ≠ v) G

    -- Show that the cardinality of V' is strictly less than the cardinality of V, a requirement for the inductive hypothesis.
    have card_V' : Fintype.card V' < Fintype.card V := by
      apply Fintype.card_subtype_lt
      simp [V']
      rfl

    -- Show that the degree condition still holds for G': the degree of any vertex in G' is less than n.
    have deg' : ∀ u : V', G'.degree u < n := by
      intro u
      rw [SimpleGraph.degree]
      let s := G'.neighborFinset u
      let t := G.neighborFinset u.val
      have h_sub : ∀ x ∈ s, x.val ∈ t := by
        intro x hx
        rw [SimpleGraph.mem_neighborFinset] at hx
        simp
        exact (mem_neighborFinset G ↑u ↑x).mpr hx
      have h_card_le : G'.degree u ≤ G.degree u.val := by
        rw [SimpleGraph.degree, SimpleGraph.degree]
        apply Finset.card_le_card_of_injOn (fun x => x.val) h_sub
        intros x₁ hx₁ x₂ hx₂ h_eq
        exact Subtype.ext h_eq
      exact lt_of_le_of_lt h_card_le (h_deg u.val)

    -- Apply the inductive hypothesis to G'.
    simp_all

    -- The inductive hypothesis guarantees that G' has a coloring c' with n colors.
    have ih_applied : Nonempty (G'.Coloring (Fin n)) := by
      apply ih (Fintype.card V') card_V'
      intro u
      exact deg' u
      rfl

    obtain ⟨c'⟩ := ih_applied

    -- Identify the colors used by the neighbors of `v` in G.
    let used_colors : Finset (Fin n) := (G.neighborFinset v).image (fun u =>
      if h : u ≠ v then c' ⟨u, h⟩ else Fin.mk 0 h_pos)

    -- The number of used colors is at most the degree of `v`.
    have h_card_used : used_colors.card ≤ G.degree v := by
      apply Finset.card_image_le

    -- The degree of `v` is strictly less than n.
    have h_deg_lt : G.degree v < n := h_deg v

    -- Prove that there exists an unused color for `v`.
    have h_exists_color : ∃ color : Fin n, color ∉ used_colors := by
      have h_card_lt : used_colors.card < Fintype.card (Fin n) := by
        rw [Fintype.card_fin]
        exact lt_of_le_of_lt h_card_used h_deg_lt
      by_contra! h_all_used
      have : used_colors = Finset.univ := Finset.eq_univ_of_forall h_all_used
      rw [this, Finset.card_univ, Fintype.card_fin] at h_card_lt
      exact Nat.lt_irrefl _ h_card_lt

    -- Pick an unused color for `v`.
    obtain ⟨color_v, h_color_v⟩ := h_exists_color

    -- Define the coloring `c` for the entire graph G: `v` gets `color_v`, other vertices get their color from `c'`.
    let c : V → Fin n :=
      fun u => if h : u = v then color_v else c' ⟨u, by
        intro h_eq; subst h_eq
        exact (h rfl).elim⟩

    -- State that we are providing `c` as the desired coloring.
    use c

    intro u w h_adj

    simp_all

    -- Now, prove that `c` is a proper coloring.
    by_cases h_u : u = v
    · -- Case: u = v
      subst h_u
      simp [c]
      have h_w_ne : w ≠ u := by
        intro h_eq
        subst h_eq
        exact G.irrefl h_adj
      simp [if_neg h_w_ne]
      have h_w_in_used : c' ⟨w, h_w_ne⟩ ∈ used_colors := by
        simp [used_colors]
        use w
        sorry
      sorry
    · -- Case: u ≠ v
      sorry
