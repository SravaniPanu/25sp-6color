import Mathlib

import Sp480b6color.Planar_defs
variable {V : Type u} {G : SimpleGraph V}
  [Fintype V] [Nonempty V] [DecidableRel G.Adj]
lemma zero_colorable (h: Planar G) (h1: Fintype.card V = 0) : G.Colorable 6 := by
    sorry

theorem Color (h: Planar G) : (G.Colorable) (6) := by
    induction' hV: Fintype.card V with n ih
    case zero =>
        exact zero_colorable h hV
    case succ =>
        obtain ⟨v0, hv0⟩ := Planar.five_or_fewer_vertex h
        sorry
