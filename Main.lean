import Mathlib

import Sp480b6color.Planar_defs
import Sp480b6color.nColor
import Sp480b6color.Subgraph

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

-- /-- 2.  If a graph `G` has a vertex `v` of degree ≤ 5 and the graph
--       obtained by deleting `v` has a 6-colouring, then so does `G`. -/
lemma Colorable.extend_degree_le_five (h : Planar G) {v:V}
    (hcol : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable 6) :
    G.Colorable 6 := sorry

lemma second_Colorable.extend_degree_le_five
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v : V} (hdeg : G.degree v ≤ 5)
    (hcol : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable 6) :
    G.Colorable 6 := by sorry

theorem Color (h: Planar G) : (G.Colorable) (6) := by
    induction' hV: Fintype.card V with n ih
    case zero =>
        exact zero_colorable h hV
    case succ =>
        obtain ⟨v0, hv0⟩ := Planar.five_or_fewer_vertex h
        obtain ⟨v, hv⟩ := Planar.five_or_fewer_vertex (G := G) h
        -- 2. colour the smaller graph

        set H : G.Subgraph := (⊤ : G.Subgraph).deleteVerts {v} with hHdef

        have hPlanarH : IsPlanar H.coe := h.delete_vertex v

        have hcard : Fintype.card H.verts = n := by sorry

        -- have hcolH : H.coe.Colorable 6 := ih hcard hPlanarH

        -- exact second_Colorable.extend_degree_le_five h v hcolH
        sorry
