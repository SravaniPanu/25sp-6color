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
lemma Colorable.extend_degree_le_five (h : Planar G)
    (hdeg :  ∃v : V, G.degree v ≤ 5 )
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
        have hcardH : Fintype.card H.verts < n.succ := by
          -- `n.succ` is `card V`; removing one vertex gives strictly fewer
          have : Fintype.card H.verts = n := by
            -- simple arithmetic
            simp [hHdef, hcardH.succ] at *
            sorry
          linarith
        -- apply IH
        have hcolH : H.coe.Colorable 6 :=
          ih (Fintype.card H.verts) hcardH _ _ _ rfl hPlanarH
        -- 3. extend the colouring over `v`
        simpa using
          Colorable.extend_degree_le_five (G := G) (v := v) hv hcolH



        -- Before:
        -- let H : G.Subgraph := (⊤ : G.Subgraph).deleteVerts {v0}

        -- have hH : IsPlanar H.coe := Planar.delete_vertex h v0

        -- have hcard : Fintype.card H.verts = n := by
        --   simpa [hV] using Fintype.card_subtype_eq (v0 : V)

        -- -- have hcard : Fintype.card H.verts = n := by
        -- --   -- partition the vertices into the deleted one and the rest
        -- --   have h := Fintype.card_subtype_compl (fun v : V => v = v0)
        -- --               -- ⬝  card {v | v = v₀} + card {v | v ≠ v₀} = card V
        -- --   -- rewrite the “deleted” part with `card_subtype_eq`
        -- --   -- and `card V` with `hV : card V = n.succ`
        -- --   simpa [H, card_subtype_eq, hV, Nat.add_comm] using h

        -- have hcolH : H.coe.Colorable 6 := by
        --   have := ih hcard
        --   exact this hH                -- IH gives the colouring

        -- -- 3.  Extend that colouring to the whole graph
        -- exact Colorable.extend_degree_le_five h hv0 hcolH




/-! #############################################
    3 ▸  The six-colour theorem
############################################# -/

theorem test_six_color
    {V : Type u} (G : SimpleGraph V)
  [Fintype V] [Nonempty V] [DecidableRel G.Adj] (h : Planar G) :
    G.Colorable 6 := by
    induction' hV: Fintype.card V with n ih
    case zero =>
        exact zero_colorable h hV
    case succ =>
      -- Empty graph is trivially 6-colourable
      simpa using zero_colorable h rfl
  | succ hcard' =>
      -- 1. pick a low-degree vertex
      obtain ⟨v, hv⟩ := Planar.five_or_fewer_vertex (G := G) hG
      -- 2. colour the smaller graph
      set H : G.Subgraph := (⊤ : G.Subgraph).deleteVerts {v} with hHdef
      have hPlanarH : IsPlanar H.coe := hG.delete_vertex v
      have hcardH : Fintype.card H.verts < n.succ := by
        -- `n.succ` is `card V`; removing one vertex gives strictly fewer
        have : Fintype.card H.verts = n := by
          -- simple arithmetic
          simp [hHdef, hcard'.succ] at *
        linarith
      -- apply IH
      have hcolH : H.coe.Colorable 6 :=
        ih (Fintype.card H.verts) hcardH _ _ _ rfl hPlanarH
      -- 3. extend the colouring over `v`
      simpa using
        Colorable.extend_degree_le_five (G := G) (v := v) hv hcolH
