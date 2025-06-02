import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset

import Sp480b6color.Planar_defs

universe u

structure IsPlanar {V : Type u} (G : SimpleGraph V)
  [Fintype V]  [DecidableRel G.Adj] : Prop where
  v_nonempty : Fintype.card V ≥ 1
  euler_constraint : G.edgeFinset.card + 2 > Fintype.card V
  face_degree_bound : (Fintype.card V ≥ 3) →
    3 * (G.edgeFinset.card + 2 - Fintype.card V) ≤ 2 * G.edgeFinset.card

namespace Planar

variable {V : Type u} {G : SimpleGraph V}
  [Fintype V] [Nonempty V] [DecidableRel G.Adj]

variable  (w : V)

-- General theorem: any subgraph of a planar graph is planar
theorem of_subgraph (hG : Planar G) (H : G.Subgraph)
  [Fintype H.verts] [DecidableRel H.coe.Adj] : IsPlanar H.coe := by
  -- The proof would involve:
  -- 1. Defining appropriate E' for H.coe from hG.E
  -- 2. Proving all the planar properties hold for the subgraph
  sorry


noncomputable
instance deleteVertsFintype (w : V) :
    Fintype ↑((⊤ : G.Subgraph).deleteVerts {w}).verts :=
  Fintype.ofFinite _

theorem delete_vertex (hG : Planar G) (w : V):
    IsPlanar ((⊤ : G.Subgraph).deleteVerts {w}).coe := by
  let H : G.Subgraph := (⊤ : G.Subgraph).deleteVerts {w}
  exact of_subgraph hG H

end Planar
