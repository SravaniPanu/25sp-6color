import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic

/-- A finite, connected simple graph is planar if there is a choice of
    edge‐finset satisfying the usual handshaking and face‐degree bounds.
    We *define* the number of faces to be `e + 2 - v`. -/
structure Planar {V : Type u} (G : SimpleGraph V)
  [Fintype V] [DecidableEq V] [DecidableRel G.Adj] where

  -- We pick out exactly which edges “live in the embedding.”
  E : Finset (Sym2 V)

  -- Connectivity needed so Euler’s formula really gives `f = e + 2 - v`.
  connected : G.Connected -- Might not work when we create disconnected...

  -- Non-empty vertices
  v_nonempty : Fintype.card V ≥ 1

  -- Face ≥ 1
  face_nonempty : E.card + 2 - Fintype.card V ≥ 1

  -- Handshaking
  handshaking : ∑ v, G.degree v = 2 * E.card

  -- Every chosen pair really is an edge of the graph.
  edges_are_graph_edges : ∀ e ∈ E, e ∈ G.edgeSet

  -- Minimum face‐degree bound for |V|≥3: ever  y face has size ≥3.
  face_degree_bound : (Fintype.card V ≥ 3) → 3 * (E.card + 2 - Fintype.card V) ≤ 2 * E.card


namespace Planar

variable {V : Type u} {G : SimpleGraph V}
  [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

-- Edges
def e (h : Planar G) : ℕ := h.E.card

lemma edges_non_negative (h : Planar G) : h.e ≥ 0 :=
  Nat.zero_le h.e

-- Vertices
def v (h : Planar G) : ℕ := Fintype.card V

lemma vertices_positive (h : Planar G) : h.v ≥ 1 := by
  exact h.v_nonempty

-- Faces defined `v - e + f = 2`.
def f (h : Planar G) : ℕ := h.e + 2 - h.v

lemma face_positive (h : Planar G): h.e + 2 - h.v > 0 :=  by
  exact h.face_nonempty

-- Euler’s formula
theorem euler_char (h : Planar G) : (h.v : ℤ) - (h.e : ℤ) + (h.f : ℤ) = 2 := by
  dsimp [e, v, f]
  let n := Fintype.card V
  let m := h.E.card

  have h_f_pos : h.f ≥ 1 := by
    apply face_positive

  have h_eq (x y: ℤ): x - y  + (y + 2 - x) = 2 := by
    ring

  -- rw [h_eq]
  sorry

end Planar



-- def f {G : SimpleGraph V} (h : Planar G) : Nat := sorry

-- #check euler_char

-- theorem five_color (G : SimpleGraph V) (h : Planar G) : Planar G := by
--   exact h
