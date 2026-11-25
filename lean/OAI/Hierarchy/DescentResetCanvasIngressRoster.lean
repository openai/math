import OAI.Hierarchy.DescentResetCanvasIngressRead
import OAI.Hierarchy.DescentStageVenuePeers
import OAI.Hierarchy.DescentPublishedHubBits
import OAI.Hierarchy.DescentResetFlowColumns

namespace OAI
/-! # The counted predecessor roster remains the physical reset roster after intake -/
namespace Hierarchy.DescentResetCanvasIngress
open DescentSixParty DescentCompiler DescentColonies DescentPacking.PackedMatch.Local.Stage
open DescentGroupPeerOrder DescentSIMDLookup DescentPackedColony DescentPackedZip ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bs : P→ℕ} {W : MarkedWorld F d P bs} {G : PoweredGadget F}
    {price ε : ℝ} {S : AtomSchedule} {k i z D wire hist H w : ℕ} (r : Reached W G price ε S k i z D wire hist)
    (wide : Fintype.card r.V≤H)
local notation "A" => r.placement
local notation "nm" => DescentResetSignedTokens.venueNames r
local notation "host" => r.vertex.trans (Fin.castLEEmb wide)

private theorem original_slot (v:r.V) (j:Fin (A).degree) :
    PackedFlow.next A nm (nm v) j=(hostRoster A (r.vertex.trans Fin.valEmbedding) v j).map nm := by
  unfold PackedFlow.next hostRoster
  rw [Equiv.symm_apply_apply]
  by_cases seen:∃u,hostSlot A (r.vertex.trans Fin.valEmbedding) v u=j
  · simp only [show PackedFlow.socket A ((nm).toEmbedding.trans Fin.valEmbedding) =
        hostSlot A (r.vertex.trans Fin.valEmbedding) from rfl, dite_eq_left seen, Option.map_some]
  · simp only [show PackedFlow.socket A ((nm).toEmbedding.trans Fin.valEmbedding) =
        hostSlot A (r.vertex.trans Fin.valEmbedding) from rfl, dite_eq_right seen, Option.map_none]

/-- The live weighted host uses the same numbered port as its original roster. -/
theorem original_port (v : r.V) (j : Fin (A).degree) :
    PackedFlow.portAt A nm v j=hostRoster A (r.vertex.trans Fin.valEmbedding) v j := by
  unfold PackedFlow.portAt
  rw [original_slot]
  cases hostRoster A (r.vertex.trans Fin.valEmbedding) v j <;> simp

theorem roster_eq (h:Fin H) (j:Fin D) :
    r.venueRoster wide h j=PackedFlow.Padded.roster (D:=D) A nm wide h j := by
  change hostRotor host (hostRoster A (r.vertex.trans Fin.valEmbedding)) h (Fin.cast r.branch.symm j)=_
  by_cases live:∃v,host v=h
  · rcases live with ⟨v,rfl⟩
    have yes:∃u,host u=host v:=⟨v,rfl⟩
    rw [hostRotor,dite_eq_left yes,(host).injective yes.choose_spec]
    change _=(DescentPackedFlowPair.Padded.project (Fintype.card r.V) ((nm v).castLE wide)).bind _
    rw [DescentPackedFlowPair.Padded.project_cast]
    have slot : DescentPackedFlowPair.Padded.project (A).degree j=some (j.cast r.branch.symm) := by
      simp [DescentPackedFlowPair.Padded.project,show j.val<(A).degree from by simpa only [r.branch] using j.isLt]
      exact Fin.ext rfl
    simp only [Option.bind_some,slot,original_slot r v (j.cast r.branch.symm),Option.map_map]
    rfl
  · rw [hostRotor,dite_eq_right live]
    have outside:¬h.val<Fintype.card r.V:=by
      intro small
      let idx:Fin (Fintype.card r.V):=⟨h.val,small⟩
      refine live ⟨(nm).symm idx,Fin.ext ?_⟩
      change ((nm) ((nm).symm idx)).val=h.val
      rw [Equiv.apply_symm_apply]
    simp [PackedFlow.Padded.roster,DescentPackedFlowPair.Padded.next,DescentPackedFlowPair.Padded.project,outside]

/-- This also carries an earlier native count word through the whole acquired chart. -/
theorem header (io:Dated.Operands) (old M short a b base:ℕ) (count : Bank) (m:Memory w)
    (seen:stageVenue r wide io old a base (r.venueRoster wide) m) (cf:count.Fits w base)
    (counted:m count.base=(Fintype.card r.V:Word w))
    (sourceRoom:∀(x:Block k)(j:Fin (2*(A).cap)),(io.wire x.val j.val).Fits w base)
    (room:(datedLayout r H old M short a b).endAddress base<2^w) :
    let L:=datedLayout r H old M short a b
    let out:=(L.phase base w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)).image m
    out count.base=(Fintype.card r.V:Word w) ∧
    (∀v:r.V,out (io.hubs.base+(nm v).val)=(((A).hub v).toNat:Word w)) ∧
    ∀h:Fin H,∀j:Fin D,out (io.roster.base+(h.val*D+j.val))=
      (target (PackedFlow.Padded.roster (D:=D) A nm wide h j):Word w) := by
  let L:=datedLayout r H old M short a b
  obtain ⟨access,observed,_,_,hf,hs,hubs,af,_⟩:=seen
  have low:=(L.any base io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)
    m hf (fun x=>af x.val) (fun t=>sourceRoom t.1 t.2) room).2
  refine ⟨(low _ (.inl (by have:=cf.1;have:=cf.2.2;omega))).trans counted,?_,?_⟩
  · intro v
    have cut := (Nat.add_lt_add_left ((host v).isLt.trans_le hs) _).trans_le hf.2.2
    exact (low _ (.inl cut)).trans ((hubs (host v)).trans (congrArg (fun n:ℕ=>(n:Word w)) (DescentHubBits.live A host v)))
  · intro h j
    have reach : h.val*D+j.val<H*D:=by
      simpa only [finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm] using (finProdFinEquiv (h,j)).isLt
    have cut:io.roster.base+(h.val*D+j.val)<base:=
      (Nat.add_lt_add_left (reach.trans_le access.rosterRoom) _).trans_le access.roster.2.2
    exact (low _ (.inl cut)).trans ((observed.roster h j).trans
      (congrArg (fun o:Option (Fin H)=>(target o:Word w)) (roster_eq r wide h j)))
private theorem padded_port_cast {D₀ D₁ : ℕ} (eqn : D₀=D₁) (v : Fin H) (j : Fin D₀) :
    PackedFlow.Padded.roster (D:=D₁) A nm wide v (j.cast eqn)=PackedFlow.Padded.roster (D:=D₀) A nm wide v j :=by
  subst D₁;rfl

/-- Reading a counted port at its original vertex-degree index restores the genuine padded roster. -/
theorem roster_at_degree (v : Fin H) (j : Fin (A).degree) :
    r.venueRoster wide v (j.cast r.branch)=PackedFlow.Padded.roster (D:=(A).degree) A nm wide v j :=
  (roster_eq r wide v _).trans (padded_port_cast r wide r.branch v j)

end
end Hierarchy.DescentResetCanvasIngress

end OAI
