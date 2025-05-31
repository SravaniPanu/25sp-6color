import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset

universe u

-- The Planar structure (simplified - removed connectivity requirement)
structure Planar {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] where
  E : Finset (Sym2 V) -- Represents edges in a specific planar embedding
  v_nonempty : Fintype.card V ≥ 1
  euler_constraint : E.card + 2 > Fintype.card V
  handshaking : ∑ v : V, G.degree v = 2 * E.card -- Sum over all vertices in the type V
  edges_are_graph_edges : ∀ e ∈ E, e ∈ G.edgeSet -- E must be a subset of actual graph edges
  face_degree_bound : (Fintype.card V ≥ 3) →
    3 * (E.card + 2 - Fintype.card V) ≤ 2 * E.card

structure IsPlanar {V : Type u} (G : SimpleGraph V)
  [Fintype V]  [DecidableRel G.Adj] : Prop where

-- v_nonempty : Fintype.card V ≥ 1
-- euler_constraint : G.edgeFinset.card + 2 > Fintype.card V
-- face_degree_bound : (Fintype.card V ≥ 3) →
--   3 * (G.edgeFinset.card + 2 - Fintype.card V) ≤ 2 * G.edgeFinset.card


namespace Planar

variable {V : Type u} {G : SimpleGraph V}
  [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

variable  (w : V)

-- General theorem: any subgraph of a planar graph is planar
theorem of_subgraph (hG : Planar G) (H : G.Subgraph)
  [Fintype H.verts] [DecidableRel H.coe.Adj] : IsPlanar H.coe := by
  -- The proof would involve:
  -- 1. Defining appropriate E' for H.coe from hG.E
  -- 2. Proving all the planar properties hold for the subgraph
  sorry


-- checking

#check G.Subgraph

#check (⊤ : G.Subgraph)

#check ((⊤ : G.Subgraph).deleteVerts {w}).coe

#check fun (w : V) => ((⊤ : G.Subgraph).deleteVerts {w}).coe

#check Fintype ((⊤ : G.Subgraph).deleteVerts {w}).verts

#check (((⊤ : G.Subgraph).deleteVerts {w}).verts)

#check Fintype ((⊤ : G.Subgraph).deleteVerts {w}).verts
-- theorem delete_vertex (hG : Planar G) (w : V) :
--   IsPlanar ((⊤ : G.Subgraph).deleteVerts {w}).coe := by
--   let H := (⊤ : G.Subgraph).deleteVerts {w}
--   -- bring the missing Fintype into scope:
--   haveI : Fintype H.verts := Fintype.subtype (fun v => v ∈ H.verts) inferInstance
--   -- now the rest follows
--   …

theorem del_vertex (hG : Planar G) (H : G.Subgraph) (w : V)
  [Fintype H.verts] [DecidableRel H.coe.Adj] :
  IsPlanar (H.deleteVerts {w}).coe := by exact of_subgraph hG (H.deleteVerts {w})

-- theorem del_vertex (hG : Planar G) (H : G.Subgraph) (w : V) [Fintype H.verts] [DecidableRel H.coe.Adj] : IsPlanar H.deleteVerts {w}  := by

--   sorry

theorem delete_vertex (hG : Planar G) (w : V):
    IsPlanar ((⊤ : G.Subgraph).deleteVerts {w}).coe := by

  let H : G.Subgraph := (⊤ : G.Subgraph).deleteVerts {w}

  exact of_subgraph hG H


end Planar
