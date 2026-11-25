import OAI.Hierarchy.DescentResetSignedMemory
import OAI.Hierarchy.DescentResetActorPlanes
import OAI.Hierarchy.DescentPackedMatchRoster
import OAI.Hierarchy.DescentDatedStageVenue

namespace OAI
/-! # The physically ranked reset packets in the next stage's compact host order -/
namespace Hierarchy.DescentSharedCableNames.Stage
open DescentSixParty DescentColonies DescentHostDirectory DescentCompiler
open DescentPacking.PackedMatch.Local
open scoped Classical
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i : ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {q ε:ℝ}
  (A:GroupStage W G q ε J V k) (edges:W.graph.Edge↪ℕ) (S:AtomSchedule) (valid:A.StateBounds S i)

theorem panel_same_order (left right:Host J V k↪ℕ)
    (ordered : ∀h:Host J V k,∀x∈near A h,∀y∈near A h,(left x<left y↔right x<right y))
    (h:Host J V k) (s:Fin (2*A.cap)) :
    signedPanel A edges S valid left h s=signedPanel A edges S valid right h s:=by
  have slots (j:↥((source A edges).incident h)) :
      (neighbors A edges left).slot h j=(neighbors A edges right).slot h j:=by
    let peer:↥(near A h):=⟨(source A edges).peer h j.val,(source A edges).peer_mem (near A) (connected A edges) h j⟩
    apply Fin.ext
    change (Ends.neighborOrder (near A) left (near_room A) h peer).val=(Ends.neighborOrder (near A) right (near_room A) h peer).val
    rw [Stage.nb_val,Stage.nb_val]
    apply congrArg Finset.card
    ext u
    simp only [Finset.mem_filter]
    exact and_congr_right (fun present=>ordered h u present peer.val peer.property)
  by_cases hit : ∃ p, signed A edges S valid h.1 h.2 p = s
  · obtain ⟨p,rfl⟩ := hit
    rw [signed_read, signed_read]
    simp only [live, slots]
  · simp only [signedPanel, dite_eq_right hit]

end
end Hierarchy.DescentSharedCableNames.Stage

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt DescentHostDirectory
open DescentPackedColony DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:AtomSchedule} {k i z D n h C f g cut tail wire hist:ℕ} {params:ResetRates G S k D n h C f g cut tail}
  {previous:Reached W G q ε S k i z D wire hist} (B:ClosedReset previous params)
  {H:ℕ} (width:Fintype.card B.next.V≤H)
local notation "A" => B.next.placement
local notation "G₁" => S.groupCount (i+1)
local notation "host" => B.next.vertex.trans (Fin.castLEEmb width)
local notation "vertex" => B.frame.host.symm.toEmbedding.trans previous.vertex
local notation "raw" => B.reset.rawHostRank B.terminals vertex
local notation "native" => B.next.order.trans Fin.valEmbedding
local notation "gid" => Function.Embedding.refl (Fin G₁)
local notation "denseNames" => cableNames k (groupRank ((gid).trans Fin.valEmbedding) ((host).trans Fin.valEmbedding))

private theorem earlier_iff (a b:B.next.V):((raw a).val<(raw b).val)↔(host a).val<(host b).val:=by
  let n:=(raw).trans Fin.valEmbedding
  have same (x:B.next.V):(host x).val=(DescentPhysicalOrder.physical n x).val:=by
    change (B.reset.denseHostRank B.terminals vertex x).val=_
    exact (B.reset.denseHostRank_read B.terminals vertex x).trans (DescentPhysicalOrder.physical_val n x).symm
  rw [same,same]
  exact (DescentPhysicalOrder.physical_lt_iff n a b).symm

set_option maxHeartbeats 1000000 in
private theorem unchanged (c:Stage.Host (Fin G₁) B.next.V k) (j:Fin (2*(A).cap)) :
    Stage.signedPanel (A) native S B.next.valid (fieldNames B) c j=Stage.signedPanel (A) native S B.next.valid denseNames c j:=by
  apply Stage.panel_same_order
  intro h x hx y hy
  obtain ⟨u,in₁,rfl⟩:=Finset.mem_map.mp hx
  obtain ⟨v,in₂,rfl⟩:=Finset.mem_map.mp hy
  obtain ⟨u,_,rfl⟩:=Finset.mem_map.mp in₁
  obtain ⟨v,_,rfl⟩:=Finset.mem_map.mp in₂
  change (_*2^k+h.2.val<_*2^k+h.2.val ↔ _*2^k+h.2.val<_*2^k+h.2.val)
  simp only [Nat.add_lt_add_iff_right,Nat.mul_lt_mul_right (Nat.two_pow_pos k)]
  change h.1.1.val * pitch ((raw).trans Fin.valEmbedding) + (raw u).val <
      h.1.1.val * pitch ((raw).trans Fin.valEmbedding) + (raw v).val ↔
    h.1.1.val * pitch ((host).trans Fin.valEmbedding) + (host u).val <
      h.1.1.val * pitch ((host).trans Fin.valEmbedding) + (host v).val
  simpa only [Nat.add_lt_add_iff_left] using earlier_iff B width u v

theorem next_signed (rack_:Fin H→Option B.next.V)
    (exists_:∀h u,rack_ h=some u→host u=h) (covers:∀u,rack_ (host u)=some u)
    (x:Block k) (j:Fin (2*(A).cap)) (h:Fin H)(grp:Fin G₁) :
    (rack_ h).bind (fun r=>Stage.signedPanel (A) native S B.next.valid (fieldNames B) ((grp,r),x) j)=
      Prepare.signed (A) native S B.next.valid gid host x j h grp :=by
  unfold Prepare.signed Prepare.spreadField
  cases tag:rack_ h with
  | none=>
    have missing:¬∃z:Fin G₁×B.next.V,gid z.1=grp ∧ host z.2=h:=by
      rintro ⟨z,_,eq⟩
      have yes:=covers z.2;rw [eq,tag] at yes;contradiction
    simp only [Option.bind_none, dite_eq_right missing]
  | some u=>
    have atHost:=exists_ h u tag
    have seen:∃z:Fin G₁×B.next.V,gid z.1=grp ∧ host z.2=h:=⟨(grp,u),rfl,atHost⟩
    have chosen:seen.choose=(grp,u):=Prod.ext seen.choose_spec.1 ((host).injective (seen.choose_spec.2.trans atHost.symm))
    simp only [Option.bind_some,dite_eq_left seen,chosen]
    exact unchanged B width _ _

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
