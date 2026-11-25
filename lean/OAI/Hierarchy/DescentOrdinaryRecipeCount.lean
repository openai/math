import OAI.Hierarchy.DescentScheduledBitHistory
import OAI.Hierarchy.DescentPickedAtomCount

namespace OAI
/-! # The actual selected bit histories add one scalar node per installed gadget party -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentSixParty DescentNetworkPartition DescentHostDirectory GadgetNetwork
open scoped Classical BigOperators
noncomputable section
variable {F P C U : Type} [Field F] [Fintype C] {D d : ℕ} {bits : P→ℕ}

theorem quotient_node_count (N : Network D P bits) (loc : N.Site→C) (pos : C→EuclideanSpace ℝ (Fin d))
    (ball : ∀v,‖pos v‖≤1) (old : SiteBits (U:=U) N) :
    (∑v,Fintype.card ((quotientBits N loc pos ball old v).Node))=∑v,Fintype.card ((old v).Node) := by
  change (∑v,Fintype.card (Σs : {i //loc i=v},(old s.val).Node))=_
  simp_rw [Fintype.card_sigma]
  rw [←Fintype.sum_sigma' (fun v (s : {i //loc i=v})=>Fintype.card (old s.val).Node)]
  exact (Equiv.sigmaFiberEquiv loc).sum_comp (fun s=>Fintype.card (old s).Node)

namespace BitDescription
variable {W : MarkedWorld F d P bits}
def nodes (B : BitDescription W) : ℕ := ∑v,Fintype.card (B.recipe v).Node

theorem selected_node_count (B : BitDescription W) {I V : Type} [Fintype I] (G : PoweredGadget F)
    (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
    (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) {Z : ℕ} (room : ∀i,z i≤Z)
    (pack : W.graph.Site→V) (p : I→Profile G.C) :
    (B.selected G pick z hz fit room pack p).nodes=B.nodes+6*Fintype.card I := by
  let widths := branchWidth G z p
  refine (quotient_node_count (physical W.graph pick widths) (newSite W.graph pick (bestLayout widths) pack)
    (fun _ => (0 : EuclideanSpace ℝ (Fin d))) (fun _ => by simp)
    (physicalBits G W.toWorld pick z room p B.recipe)).trans ?_
  change (∑v : W.graph.Site⊕(I×Fin 6),Fintype.card ((physicalBits G W.toWorld pick z room p B.recipe v).Node))=_
  rw [Fintype.sum_sum_type]
  have one (v : I×Fin 6) : Fintype.card ((physicalBits G W.toWorld pick z room p B.recipe (.inr v)).Node)=1 := by
    change Fintype.card Unit=1
    simp
  simp_rw [one]
  simp [nodes,physicalBits,BitRecipe.retag,BitRecipe.reroute,Nat.mul_comm]
  refine Finset.sum_congr (by ext v; simp only [Finset.mem_univ]) ?_
  intro v _
  exact @Fintype.card_congr _ _ _ _ (Equiv.refl (B.recipe v).Node)

theorem coalesced_node_count (B : BitDescription W) {V : Type} [DecidableEq V]
    (key : W.graph.Site→Key V) (flag : V→Bool) (k g : ℕ) : (B.coalesced key flag k g).nodes=B.nodes :=
  quotient_node_count _ _ _ _ B.recipe

theorem renamed_node_count (B : BitDescription W) (s : Equiv.Perm W.graph.Site)
    (e : Equiv.Perm W.graph.Edge) : (B.renamed s e).nodes=B.nodes :=
  s.symm.sum_comp (fun v=>Fintype.card (B.recipe v).Node)

theorem follow_node_count (n : Normalize W) (B : BitDescription W) : (follow n B).nodes=B.nodes := by
  induction n with
  | done => rfl
  | split W q m fit rest ih => exact ih _
  | merge W V key flag k g rest ih => exact (ih _).trans (coalesced_node_count B key flag k g)
  | named W s e rest ih => exact (ih _).trans (renamed_node_count B s e)

variable {G : PoweredGadget F} {u ε : ℝ} (he : 0≤ε) (T : StageInput W G u ε)

theorem scanned_node_count (B : BitDescription W) (p : (T.result he).Choice) :
    (scanned he T B p).nodes=B.nodes+6*Fintype.card (scannedRows he T).pairs := by
  let r := scannedRows he T
  have cast_nodes {X Y : MarkedWorld F d P bits} (eqn : X=Y) (O : BitDescription X) :
      (cast (congrArg BitDescription eqn) O).nodes=O.nodes := by subst Y;rfl
  dsimp only [scanned]
  refine (cast_nodes (r.state p).symm (B.selected G r.pick (fun _ => T.z)
    (fun _ => T.unitPos) r.fit (fun _ => le_refl T.z) r.pack (r.profile p))).trans ?_
  exact B.selected_node_count G r.pick (fun _ => T.z) (fun _ => T.unitPos) r.fit
    (fun _ => le_refl T.z) r.pack (r.profile p)

theorem scanned_node_bound (B : BitDescription W) (p : (T.result he).Choice) :
    (scanned he T B p).nodes≤B.nodes+6*(W.liveWidth/(2*(T.z*G.b))) := by
  let r := scannedRows he T
  rw [scanned_node_count]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 6 (W.paired_count_le r.pick r.picked T.z G.b
    (Nat.mul_pos T.unitPos (by have :=G.paid;omega)) r.fit)) _

end BitDescription
end
end Hierarchy.DescentKernelHistory

end OAI
