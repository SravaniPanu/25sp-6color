import Mathlib

/-- A finite, connected simple graph is planar if there is a choice of
    edge‐finset satisfying the usual handshaking and face‐degree bounds.
    We *define* the number of faces to be `e + 2 - v`. -/
structure Planar {V : Type u} (G : SimpleGraph V)
  [Fintype V] [Nonempty V] [DecidableRel G.Adj] where

  -- We pick out exactly which edges “live in the embedding.”
  E : Finset (Sym2 V)

  -- Connectivity needed so Euler’s formula really gives `f = e + 2 - v`.
  -- connected : G.Connected -- Might not work when we create disconnected...

  -- Non-empty vertices
  v_nonempty : Fintype.card V ≥ 1

  -- Euler constraint
  euler_constraint : E.card + 2 > Fintype.card V

  -- Every chosen pair really is an edge of the graph.
  edges_are_graph_edges : ∀ e ∈ E, e ∈ G.edgeSet

  -- Minimum face‐degree bound for |V|≥3: ever  y face has size ≥3.
  face_degree_bound : (Fintype.card V ≥ 3) → 3 * E.card + 6 - 3 * Fintype.card V ≤ 2 * E.card

  euler_corollary : G.edgeFinset.card ≤ 3 * Fintype.card V - 6


namespace Planar

variable {V : Type u} {G : SimpleGraph V}
  [Fintype V] [Nonempty V] [DecidableRel G.Adj]

-- Edges
def e (h : Planar G) : ℕ := h.E.card

lemma edges_non_negative (h : Planar G) : h.e ≥ 0 :=
  Nat.zero_le h.e

-- Vertices
def v (h : Planar G) : ℕ := Fintype.card V

lemma vertices_positive (h : Planar G) : h.v ≥ 1 := by
  exact h.v_nonempty

-- Faces defined `v - e + f = 2`.
def f (h : Planar G) : ℤ := (h.e : ℤ) + 2 - (h.v : ℤ)

lemma face_positive (h : Planar G): h.e + 2 - h.v > 0 :=  by
  exact Nat.sub_pos_of_lt (Nat.add_lt_add_right h.euler_constraint 0)

-- Euler’s formula

theorem euler_char (h : Planar G) : (h.v : ℤ) - (h.e : ℤ) + (h.f : ℤ) = 2 := by
  dsimp [e, v, f]
  ring
#check G.sum_degrees_eq_twice_card_edges
#check G.maxDegree_lt_card_verts
#check Finset.sum_univ_pi


theorem five_or_fewer_vertex (h : Planar G): ∃v : V, G.degree v ≤ 5 := by
  by_contra a
  simp_all


  -- Total degree must be lower bounded by the sum of degree of the vertices
  have h1: ∑ v, G.degree v ≥ 6 * Fintype.card V := by
    have h1a: ∀ v, G.degree v ≥ 6 := by
      intro v
      exact Nat.lt_iff_add_one_le.mp (a v)
    have h1b: ∑ v: V, G.degree v ≥ ∑ v : V, 6 := by
      exact Finset.sum_le_sum fun i a_1 => a i
    have h1c: ∑ v : V, 6 = 6 * Fintype.card V := by
      -- induction' (Fintype.card V) with n ih

      have V_finset : Finset V := Finset.univ
      have h1c1 := @Finset.sum_const _ _ V_finset _ 6
      simp
      ring
    linarith

  -- Invoke handshaking lemma
  have h2:  2 * G.edgeFinset.card ≥ 6 * Fintype.card V := by
    have: ∑ v, G.degree v = 2 * G.edgeFinset.card := by
      exact SimpleGraph.sum_degrees_eq_twice_card_edges G
    linarith

  -- Use e ≤ 3v - 6  to prove that the degree calculated using edges is
  have h3: G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
    exact h.euler_corollary

  -- Simplify h2
  have h4: G.edgeFinset.card ≥ 3*Fintype.card V := by
    linarith

  -- Trivial result for combining our two inequalities
  have h5: 3 * Fintype.card V - 6 < 3 * Fintype.card V := by
    simp_all only [ge_iff_le, tsub_lt_self_iff, Nat.ofNat_pos, mul_pos_iff_of_pos_left, and_true]
    exact h.v_nonempty
  -- Combine inequalities to create a contradiction
  linarith

#check euler_char


end Planar

-- theorem five_color (G : SimpleGraph V) (h : Planar G) : Planar G := by
--   exact h
