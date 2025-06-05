import Mathlib

import Sp480b6color.Planar_defs
import Sp480b6color.nColor
import Sp480b6color.Subgraph

variable {V : Type u} {G : SimpleGraph V}
  [Fintype V] [Nonempty V] [DecidableRel G.Adj]

-- Base Case
lemma zero_colorable (h : Planar G) (h1 : Fintype.card V = 0) :
    G.Colorable 6 := by
  classical
  -- `card = 0` ↔ `IsEmpty`; turn it into an instance so Lean can use it.
  haveI : IsEmpty V := (Fintype.card_eq_zero_iff).1 h1

  have hdeg : ∀ v : V, G.degree v < 6 := by
    intro v
    exact (IsEmpty.false v).elim     -- `v` cannot exist.

  -- Apply the bounded-degree colouring theorem you already stated.
  have : Nonempty (G.Coloring (Fin 6)) :=
    coloring_of_bounded_degree G 6 hdeg (by decide)

  simpa [SimpleGraph.Colorable] using this

-- If a graph `G` has a vertex `v` of degree ≤ 5 and the graph
-- obtained by deleting `v` has a 6-colouring, then so does `G`.

lemma Colorable.extend_degree_le_five (h : Planar G) {v:V}
    (hcol : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable 6) :
    G.Colorable 6 := sorry

theorem Color (h: Planar G) : (G.Colorable) (6) := by
    induction' hV: Fintype.card V with n ih
    -- Base Case
    case zero =>
        exact zero_colorable h hV
    -- Induction Step (All Planar graphs with n+1 vertices are colorable)
    case succ =>
        -- Get the vertex from the planar graph with degree ≤ 5
        obtain ⟨v, hv⟩ := Planar.five_or_fewer_vertex (G := G) h

        -- Remove vertex from planar graph to create subgraph H
        set H : G.Subgraph := (⊤ : G.Subgraph).deleteVerts {v} with hHdef

        -- Show that this subgraph is still Planar
        have hPlanarH : IsPlanar H.coe := h.delete_vertex v

        -- Show that this subgraph has n vertices
        have hcard : Fintype.card H.verts = n := by sorry

        -- To Do:
        have hcolH : H.coe.Colorable 6 := ih hcard hPlanarH

        -- exact second_Colorable.extend_degree_le_five h v hcolH

        sorry
