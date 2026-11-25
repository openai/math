import OAI.Hierarchy.DescentDatedRegisteredHeaders
import OAI.Hierarchy.DescentOrdinaryMountedBirth

namespace OAI
/-! # Recovering the measured input chip and its room from the actual earlier donor tape -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentRawCablePanel DescentDatedAddressBook DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentPacking.PackedMatch.Local.Stage.Chooser ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)

theorem into_booked_headers (floor : ℕ) :
    v.signedEnd floor≤v.refsStart floor ∧ v.refsStart floor≤v.vectorStart floor ∧
    v.vectorStart floor≤v.originMouthEnd floor ∧ v.originMouthEnd floor≤v.operandPathStart floor ∧
    v.operandPathStart floor≤v.operandHeaderEnd floor ∧ v.materialStart floor≤v.signedEnd floor :=by
  have a : v.birthStart floor≤v.vectorStart floor:=by rw [vectorStart,v.bornBook.affine];exact Nat.le_add_right ..
  have c : v.routedStart floor≤v.originPortEnd floor:=by rw [v.originPort_span];exact Nat.le_add_right ..
  have e : v.originMouthEnd floor≤v.operandPathStart floor:=by
    rw [operandPathStart,DescentDatedOperandPages.affine];exact Nat.le_add_right ..
  have f : v.operandPathStart floor≤v.operandRankStart floor:=(Nat.le_add_right ..).trans (DescentDatedSourcePathDirectory.end_le ..)
  have g : v.operandRankStart floor≤v.operandOldHeaderStart floor:=Nat.le_add_right ..
  have i : v.operandOldHeaderStart floor≤v.operandHeaderEnd floor:=(Nat.le_add_right _ _).trans (Nat.le_add_right ..)
  have before : v.materialStart floor≤v.materialEnd floor:=by rw [materialEnd,v.material.translated];exact Nat.le_add_right ..
  have above:=v.signed_stage_paid floor
  exact ⟨Nat.le_add_right ..,(Nat.le_add_right ..).trans a,(v.vector_before floor).trans (c.trans (Nat.le_add_right ..)),
    e,f.trans (g.trans i),before.trans (above.2.1.trans above.2.2)⟩

namespace ArgumentEntry
variable (A : ArgumentEntry v)
theorem mounted_header_chip {w : ℕ} (floor : ℕ) (m : Memory w) (shape : A.BirthShape v) (mat : A.Match v floor)
    (safe : A.Room v floor w) (positive : 0<A.clip.panelPitch)
    (parts : Fin A.clip.venue.hosts→Fin A.clip.venue.groups→DepotRAM.Parts A.clip.venue.socket)
    (issued : Reads A.venue.panel (fun h g=>DepotRAM.combine A.clip.venue.socket (parts h g)) A.clip.panelPitch m)
    (space : v.vectorStart floor<2^w) :
    let B:=A.chipBank v floor
    B.Fits w (v.vectorStart floor) ∧ v.bornBook.rows≤B.size ∧
    Reads B (A.nativeChips v shape parts) v.bornBook.lanes (A.mountedTape v floor m) :=by
  intro B
  have fit:=A.chip_fits v floor safe mat
  have size : (A.chip v).rows≤B.size:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  change A.clip.venue.hosts * chunks A.clip.venue.groups A.clip.working ≤ B.size at size
  have span : v.bornBook.rows≤B.size:=by
    simpa only [DescentOrdinaryBorn.Chart.rows,shape.hosts,shape.groups,mat.bornPitch] using size
  have observed:=reads_at shape.hosts shape.groups shape.width mat.bornPitch (A.chip_final v floor m safe positive parts issued)
  have mount:=v.mount_run floor B ((A.inlet v floor w).image m) fit space
  exact ⟨bank_before fit (v.into_booked_headers floor).2.1,span,
    reads_through observed fit.2.2 span (fun i hi=>mount.2.2.1 i (.inl hi))⟩

end ArgumentEntry
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
