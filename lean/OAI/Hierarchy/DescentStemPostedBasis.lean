import OAI.Hierarchy.DescentDateStemRegisterRead
import OAI.Hierarchy.DescentPhysicalPublicOriginalFrame
import OAI.Hierarchy.DescentPhysicalResetDateOutput

namespace OAI
/-! # The saved physical basis and the fourth peer register at stem entry -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSIMDLookup DescentPackedZip DescentDatedAddressBook
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
variable {a : PhysicalReset} {start Wd : ℕ} (u : a.DateInputs start Wd)

structure PostedStemBasis (m : Memory Wd) : Prop where
  chosen : u.masked.image (u.privateResult m) u.originalBasis.base =
    ((DescentExterior.matrixCode B.frame.basis).val : Word Wd)
  saved : u.originalBasis.Fits Wd (a.successor.sheets.metaEnd (a.successor.remap (a.rebased start)).endAddress)
  space : a.successor.sheets.coordinateEnd (a.successor.remap (a.rebased start)).endAddress < 2^Wd
  bf : (a.successor.peerAux (a.rebased start) 3).Fits Wd
    (a.successor.sheets.metaEnd (a.successor.remap (a.rebased start)).endAddress)

private theorem basis_ordinal {x y : ℕ} (dim : x=y) (μ : DescentGL.Layout x) (ν : DescentGL.Layout y)
    (same : HEq μ ν) : (DescentExterior.matrixCode μ).val = (DescentExterior.matrixCode ν).val := by
  subst y
  rw [eq_of_heq same]

/-- The selected stencil matrix, its word in the measured image, and the lower frame
of the actor directory are the three outputs used from `fromNamed_venue_matrix`. -/
theorem stem_posted_basis (ok : u.Ready) (measured m : Memory Wd) {dim : ℕ} (μ : DescentGL.Layout dim)
    (width : dim=B.reset.k) (won : HEq μ B.frame.basis)
    (raw : measured u.originalBasis.base=((DescentExterior.matrixCode μ).val:Word Wd))
    (frame : ∀ j, j < (a.rootPhase u.shape start u.count u.hub u.g u.Y u.roots Wd).origin → m j=measured j) :
    PostedStemBasis B u m := by
  let v := a.successor
  let b := a.rebased start
  let area := (v.remap b).endAddress
  let base := v.sheets.metaEnd area
  let s := v.sheets
  let rc := a.rootPhase u.shape start u.count u.hub u.g u.Y u.roots Wd
  let f₀ := v.actorEnd b
  let addr := u.originalBasis.base
  have savedRoot : addr < rc.origin := PhysicalReset.stencil_saved_before (u:=u)
  have root : rc.origin ≤ v.middle.stop b := by
    rw [←ok.rootEnd]
    have lim := u.book.limits rc.projectionEnd v.middle.signedHosts (2^v.middle.stencil.c) v.middle.signedLanes
    exact rc.origin_le_projection.trans ((lim.1.trans (lim.2.1.trans lim.2.2)).trans (Nat.le_add_right ..))
  have actor : v.middle.stop b ≤ f₀ := by
    change v.middle.stop b ≤ v.actorEnd b
    rw [ResetOutput.actorEnd,v.actor.translated]
    omega
  have addrActor := savedRoot.trans_le (root.trans actor)
  have actorTrunk : f₀ ≤ v.trunkEnd b := by
    rw [ResetOutput.trunkEnd,v.front.trunk_shift]
    omega
  have trunkJoint : v.trunkEnd b ≤ v.jointEnd b := ok.ordered.2.2.2.1.trans (v.receipt_order b).1
  have jointBase : v.jointEnd b ≤ base := by
    change v.jointEnd b ≤ s.metaEnd area
    rw [←u.masks_end]
    exact ((v.receipt_order b).2.trans u.masked.ordered.1).trans u.masked.ordered.2
  have gate : base ≤ s.coordinateEnd area := by
    change s.metaEnd area ≤ s.coordinateEnd area
    rw [CandidateSheets.coordinateEnd,s.stemSources.extent]
    exact Nat.le_add_right ..
  have lower : s.coordinateEnd area ≤ s.inputDonorsEnd area := by rw [s.donors_shift]; omega
  have space := lower.trans_lt ok.numbers.donor.room
  have addrTrunk := addrActor.trans_le actorTrunk
  have addrBase := addrTrunk.trans_le (trunkJoint.trans jointBase)
  have suffix := (s.stemSources.any base (u.masked.image (u.privateResult m)) space).2.2 addr (.inl addrBase)
  have unchanged := (u.public_original_frame ok m addr (addrBase.trans_le gate)).symm.trans
    (u.public_original_scene ok m addr addrTrunk)
  have early := (v.front.trunkScene_any f₀ (v.issuedScene b u.earlier) u.sceneFits m ok.trunk).2 addr (.inl addrActor)
  have original := (suffix.symm.trans unchanged).trans (early.trans (frame addr savedRoot))
  have top := gate.trans_lt space
  refine ⟨original.trans (raw.trans (congrArg (fun j : ℕ => (j : Word Wd))
    (basis_ordinal (width.trans B.keyWidth) μ B.frame.basis won))), ?_, space, ?_⟩
  · change 0 < 2^0 ∧ 2^0 < 2^Wd ∧ addr+2^0 ≤ base
    rw [pow_zero]
    exact ⟨by decide, by omega, by omega⟩
  · exact ProtocolRAMGeneratedWrite.fits_mono _ jointBase (v.aux_fits b ok.packed (3 : Fin 4))

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
