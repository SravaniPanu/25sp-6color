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

-- /-- 1.  Deleting a vertex of a planar graph leaves a planar graph.
--       (You already sketched this as `Planar.delete_vertex`; just
--       keep it as a `sorry` for now.) -/
-- lemma Planar.delete_vertex
--     (hG : Planar G) (v : V) :
--     Planar ((⊤ : G.Subgraph).deleteVerts {v}).coe := sorry

-- /-- 2.  If a graph `G` has a vertex `v` of degree ≤ 5 and the graph
--       obtained by deleting `v` has a 6-colouring, then so does `G`. -/
-- lemma Colorable.extend_degree_le_five
--     {V : Type*} {G : SimpleGraph V} {v : V}
--     (hdeg : G.degree v ≤ 5)
--     (hcol : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable 6) :
--     G.Colorable 6 := sorry


theorem Color (h: Planar G) : (G.Colorable) (6) := by
    induction' hV: Fintype.card V with n ih
    case zero =>
        exact zero_colorable h hV
    case succ =>
        obtain ⟨v0, hv0⟩ := Planar.five_or_fewer_vertex h

        let H : G.Subgraph := (⊤ : G.Subgraph).deleteVerts {v0}

        have hH : IsPlanar H.coe := Planar.delete_vertex h v0

        have hcard : Fintype.card H.verts = n := by
          simpa [hV] using Fintype.card_subtype_eq (v0 : V)

        -- have hcard : Fintype.card H.verts = n := by
        --   -- partition the vertices into the deleted one and the rest
        --   have h := Fintype.card_subtype_compl (fun v : V => v = v0)
        --               -- ⬝  card {v | v = v₀} + card {v | v ≠ v₀} = card V
        --   -- rewrite the “deleted” part with `card_subtype_eq`
        --   -- and `card V` with `hV : card V = n.succ`
        --   simpa [H, card_subtype_eq, hV, Nat.add_comm] using h

        have hcolH : H.coe.Colorable 6 := by
          have := ih hcard
          exact this hH                -- IH gives the colouring

        -- 3.  Extend that colouring to the whole graph
        exact Colorable.extend_degree_le_five hv0 hcolH
