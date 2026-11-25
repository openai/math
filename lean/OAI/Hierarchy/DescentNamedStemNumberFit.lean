import OAI.Hierarchy.DescentStemNumberBounds
import OAI.Hierarchy.DescentPhysicalSheetRoom
import OAI.Hierarchy.DescentPhysicalResetDateOutput

namespace OAI
/-! # The six stem expressions retained by the dated original-ordinal program -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSIMDLookup DescentPackedZip DescentDyadicSpan DescentResetStemPackedIssue
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "s" => (v).sheets
local notation "F" => (v).front
local notation "b" => a.rebased floor
local notation "r" => ((v).remap b).endAddress
local notation "f₀" => (v).actorEnd b
local notation "origin" => (s).metaEnd r
local notation "top" => (s).publicFormatEnd r
local notation "P" => a.stencilPhase u.shape floor u.count u.hub u.g u.Y
local notation "rc" => a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
local notation "plan" => (s).stemSources
local notation "scene" => (v).issuedScene b u.earlier

theorem stem_registers_fit (rootEnd : (rc).preparedEnd u.book=(v).middle.stop b)
    (space : top<2^w) (x j : ℕ) (i : Fin 6) : (u.stemRegisters x j i).Fits w top:=by
  have last : (s).coordinateEnd r≤top:=by
    have prior : (s).coordinateEnd r≤(s).inputDonorsEnd r:=by rw [CandidateSheets.donors_shift];omega
    have donor : (s).inputDonorsEnd r≤(s).donorEnd r:=Nat.le_add_right ..
    exact prior.trans (donor.trans (Nat.le_add_right ..))
  have gate : origin≤(s).coordinateEnd r:=by rw [CandidateSheets.coordinateEnd,(s).stemSources.extent];omega
  have metaSpace:=gate.trans_lt (last.trans_lt space)
  have channel:=(v).receipt_order b
  let layer : DescentResetCandidateDate.Mixed :=
    {first:=r,jobs:=(s).jobs,lanes:=(s).lanes,hosts:=(s).hosts,groups:=(s).groups,
     bits:=(s).metaBits,rankReads:=fun _ _=>.lit 0,rawReads:=fun _ _=>.lit 0}
  have mixed : r≤origin:=layer.ordered.1.trans layer.ordered.2
  have rect : (v).privateEnd b≤r:=Nat.le_add_right ..
  have joint : (v).jointEnd b≤origin:=channel.2.trans (rect.trans mixed)
  have before : (v).trunkEnd b≤(v).massEnd b:=by unfold ResetOutput.massEnd;rw [(v).contactShape.translate];omega
  have trunk : (F).trunkEnd f₀≤origin:=before.trans (channel.1.trans joint)
  have floorLow : f₀≤(v).trunkEnd b:=by rw [ResetOutput.trunkEnd,(F).trunk_shift];omega
  have roots : (rc).origin≤(v).middle.stop b:=by
    rw [←rootEnd]
    have lim:=u.book.limits (rc).projectionEnd (v).middle.signedHosts (2^(v).middle.stencil.c) (v).middle.signedLanes
    exact (rc).origin_le_projection.trans ((lim.1.trans (lim.2.1.trans lim.2.2)).trans (Nat.le_add_right ..))
  have front : (v).middle.stop b≤f₀:=by rw [ResetOutput.actorEnd,(v).actor.translated];omega
  have keyLoc:(P).saved<origin:=(stencil_saved_before (u:=u)).trans_le (roots.trans (front.trans (floorLow.trans trunk)))
  have key : (⟨(P).saved,0⟩:Bank).Fits w origin:=by
    change 0<2^0 ∧ 2^0<2^w ∧ (P).saved+2^0≤origin
    rw [pow_zero]
    exact ⟨by decide,by omega,by omega⟩
  have raw : ((F).parent f₀).base+span (F).newHosts≤(F).parentEnd f₀:=
    Nat.add_le_add_left (Nat.le_max_right _ _) _
  have fmt : Mixed.Projected.extent ((F).parentEnd f₀) ((F).parent f₀).base (F).peer.oldDegree (F).stemField
      (F).metaBits (F).oldTicketCount (F).peer.oldHosts (F).newHosts (F).peer.groups (F).blocks (F).oldLanes
      (F).peer.lanes (F).signedQueries=(F).mixed f₀:=by
    unfold Mixed.Projected.extent Mixed.Projected.splitAt CandidateFront.mixed CandidateFront.projected
    rw [(scene).stems.queries,(scene).stems.digits]
  have beforeRows : (F).mixed f₀≤(F).gathered f₀:=by
    change _≤(F).mixed f₀+span (F).newHosts+DescentResetStemKeyReindex.size (F).newHosts (F).newHosts
      (F).peer.groups (F).peer.lanes+span ((F).newHosts*chunks (F).peer.groups (F).peer.lanes)
    omega
  have «prefix» : (F).mixed f₀≤origin:=beforeRows.trans ((Nat.le_add_right ..).trans trunk)
  have own:=(v).aux_fits b (joint.trans_lt metaSpace) (3:Fin 4)
  unfold stemRegisters
  split
  · rename_i hx
    split
    · rename_i hj
      have signed:=Mixed.Projected.signed_register_fits (D:=(F).peer.oldDegree) (f:=(F).stemField)
        (Q:=(F).signedQueries) ((F).parentEnd f₀) ((F).parent f₀).base (F).oldTicketCount (F).peer.oldHosts
        (F).newHosts (F).peer.groups (F).blocks (F).oldLanes (F).peer.lanes (F).metaBits ⟨x,hx.1⟩ ⟨j,hj.1⟩ raw
        ((fmt.le.trans «prefix»).trans_lt metaSpace)
      exact ProtocolRAMGeneratedWrite.fits_mono _ last ((plan).all_fit origin _ _ _ _ _ _
        (ProtocolRAMGeneratedWrite.fits_mono _ (fmt.le.trans «prefix») signed)
        (ProtocolRAMGeneratedWrite.fits_mono _ joint own)
        (ProtocolRAMGeneratedWrite.fits_mono _ trunk ((F).stem_operand_fits f₀ scene
          (trunk.trans_lt metaSpace) ⟨x,hx.1⟩ ⟨j,hj.1⟩)) key (last.trans_lt space) i)
    · trivial
  · trivial

/-- All six expressions read a bounded number of cells, independently of the
old cap, coordinate pitch, and total number of candidate rows. -/
theorem stem_registers_work (x j : ℕ) (t : Fin 6) : (u.stemRegisters x j t).work≤64:=by
  unfold stemRegisters
  split
  · split
    · fin_cases t <;> exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
  · exact of_decide_eq_true rfl

theorem marked_read_work (x j : ℕ) : (u.markRead x j).work=7:=rfl

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
