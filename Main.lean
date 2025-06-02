import Mathlib

import Sp480b6color.Planar_defs
import Sp480b6color.nColor

variable {V : Type u} {G : SimpleGraph V}
  [Fintype V] [Nonempty V] [DecidableRel G.Adj]

lemma zero_colorable (h : Planar G) (h1 : Fintype.card V = 0) :
    G.Colorable 6 := by
  classical
  -- `card = 0` ↔ `IsEmpty`; turn it into an instance so Lean can use it.
  haveI : IsEmpty V := (Fintype.card_eq_zero_iff).1 h1

  -- With no vertices every degree is trivially < 6.
  have hdeg : ∀ v : V, G.degree v < 6 := by
    intro v
    exact (IsEmpty.false v).elim     -- `v` cannot exist.

  -- Apply the bounded-degree colouring theorem you already stated.
  have : Nonempty (G.Coloring (Fin 6)) :=
    coloring_of_bounded_degree G 6 hdeg (by decide)

  -- `Colorable 6` is definitionally that non-emptiness.
  simpa [SimpleGraph.Colorable] using this


theorem Color (h: Planar G) : (G.Colorable) (6) := by
    induction' hV: Fintype.card V with n ih
    case zero =>
        exact zero_colorable h hV
    case succ =>
        obtain ⟨v0, hv0⟩ := Planar.five_or_fewer_vertex h
        sorry
