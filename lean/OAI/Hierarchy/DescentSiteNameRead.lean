import OAI.Hierarchy.DescentGroupNextDigit
import OAI.Hierarchy.DescentGroupSiteOrder
import OAI.Hierarchy.DescentNamedGeometry
import OAI.Hierarchy.DescentRosterOrder

namespace OAI
/-! # The named successor sites fit the dense host budget after host compaction -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentColonies DescentPacking DescentRosterOrder DescentStageEdgeReceipt
open scoped Classical BigOperators
noncomputable section
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k groups : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}

omit [DecidableEq V] in
private theorem compact_lt (rank : V↪ℕ) (a b : V) : (compact rank a).val<(compact rank b).val ↔ rank a<rank b := by
  have read (x : V) : (compact rank x).val=(DescentPhysicalOrder.physical rank x).val :=
    (compact_read rank x).trans (DescentPhysicalOrder.physical_val rank x).symm
  rw [read,read]
  exact DescentPhysicalOrder.physical_lt_iff rank a b

/-- Sparse and compact host numbers order the same group, host and block
triples. Thus a named site's semantic ID is the exact output of the native
site census in a `groups * card V * 2^k` public directory. -/
theorem siteNamed_read (A : GroupStage W G q ε (Fin groups) V k) (rank : V↪ℕ)
    (coordinates : Function.Injective (fun v=>(A.pos v,A.block v))) (named : A.SiteNamed (groupRank Fin.valEmbedding rank))
    (u : W.graph.Site) : originalId W.graph.Site u=(A.site (compact rank) coordinates u).val := by
  let raw := groupRank (Fin.valEmbedding (n:=groups)) rank
  let flat (x : W.graph.Site) := (A.pos x).1.val*Fintype.card V+(compact rank (A.pos x).2).val
  have space (v : V) : rank v<pitch rank := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ v))
  have cell (x y : W.graph.Site) : raw (A.pos x)<raw (A.pos y) ↔ flat x<flat y := by
    change (A.pos x).1.val*pitch rank+rank (A.pos x).2 < (A.pos y).1.val*pitch rank+rank (A.pos y).2 ↔
      (A.pos x).1.val*Fintype.card V+(compact rank (A.pos x).2).val < (A.pos y).1.val*Fintype.card V+(compact rank (A.pos y).2).val
    rw [nextDigit (space _) (space _),nextDigit (compact rank (A.pos x).2).isLt (compact rank (A.pos y).2).isLt,
      compact_lt]
  have same (x y : W.graph.Site) : raw (A.pos x)=raw (A.pos y) ↔ flat x=flat y := by
    have xy := cell x y
    have yx := cell y x
    omega
  rw [named u,site_val]
  congr 1
  ext v
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,siteSlot_val]
  change raw (A.pos v)*2^k+(A.block v).val < raw (A.pos u)*2^k+(A.block u).val ↔
      flat v*2^k+(A.block v).val < flat u*2^k+(A.block u).val
  rw [nextDigit (A.block v).isLt (A.block u).isLt,nextDigit (A.block v).isLt (A.block u).isLt,cell,same]

/-- The recorded dense census can be used directly as the named chart required
by the next ordinary chooser, even if the common host type is empty. -/
theorem siteNamed_of_read (A : GroupStage W G q ε (Fin groups) V k)
    (vertex : V↪Fin (Fintype.card V)) (coordinates : Function.Injective (fun v=>(A.pos v,A.block v)))
    (read : ∀u,originalId W.graph.Site u=(A.site vertex coordinates u).val) :
    A.SiteNamed (groupRank Fin.valEmbedding (vertex.trans Fin.valEmbedding)) := by
  let rank:=vertex.trans Fin.valEmbedding
  let a (u : W.graph.Site):=(A.pos u).1.val
  let b (u : W.graph.Site):=(vertex (A.pos u).2).val
  let raw (u : W.graph.Site):=a u*pitch rank+b u
  let flat (u : W.graph.Site):=a u*Fintype.card V+b u
  have lim (u : W.graph.Site) : b u<pitch rank := by
    change rank (A.pos u).2 < Finset.univ.sup (fun v => rank v) + 1
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun v => rank v) (Finset.mem_univ (A.pos u).2))
  have dense (u : W.graph.Site) : b u<Fintype.card V:=(vertex (A.pos u).2).isLt
  have order (u v : W.graph.Site) : flat u<flat v ↔ raw u<raw v := by
    dsimp only [flat,raw]
    rw [nextDigit (dense u) (dense v),nextDigit (lim u) (lim v)]
  have same (u v : W.graph.Site) : flat u=flat v ↔ raw u=raw v := by
    have uv:=order u v
    have vu:=order v u
    omega
  intro u
  rw [read,site_val]
  congr 1
  ext v
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,siteSlot_val]
  change flat v*2^k+(A.block v).val < flat u*2^k+(A.block u).val ↔
    raw v*2^k+(A.block v).val < raw u*2^k+(A.block u).val
  rw [nextDigit (A.block v).isLt (A.block u).isLt,nextDigit (A.block v).isLt (A.block u).isLt,order,same]

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
