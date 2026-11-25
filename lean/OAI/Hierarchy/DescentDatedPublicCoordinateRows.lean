import OAI.Hierarchy.DescentPublicOperandCoordinateFrame
import OAI.Hierarchy.DescentStemPostedBasis
import OAI.Hierarchy.DescentPhysicalMixedCapture

namespace OAI
/-! Paid auxiliary and coordinate inputs of the native public reset operand lookup. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSIMDLookup DescentPackedZip DescentDatedAddressBook DescentColonies
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "s" => (v).sheets
local notation "area" => ((v).remap b).endAddress
local notation "q" => (s).stemSources.coord
local notation "base" => (s).metaEnd area
local notation "deck" => (s).coordinateEnd area
local notation "first" => (v).operandFloor b

private theorem deck_fits_at_operand (ok : u.Ready) : deck≤first:=by
  have afterSheets : (v).sheetsStart b≤(v).candidateEnd b:=by
    rw [←ok.matched];exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  exact (coordinate_before_sheets (a := a) (floor := floor)).trans (afterSheets.trans ((v).operands_after_front b).2.2.2.1)

theorem public_coordinate_rows (ok : u.Ready) (m : Memory w) (basis : DescentGL.Layout (q).dim)
    (chosen : u.masked.image (u.privateResult m) u.originalBasis.base=
      ((DescentExterior.matrixCode basis).val:Word w))
    (saved : u.originalBasis.Fits w base) (space : deck<2^w) (j : Fin 3)
    (block : Fin (2^(q).fine)) (lo : Fin (2^(q).residual)) :
    let e:=(q).src base u.originalBasis j block lo
    e.Fits w first ∧ Source e (fun (_:Fin (q).hosts) g=>
      ((q).value basis j block lo g : Cell (q).width)) (q).lanes (u.beforeSetupImage ok m):=by
  have r:=(s).stemSources.coordinates base u.originalBasis (u.masked.image (u.privateResult m))
    basis chosen saved space j block lo
  exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (u.deck_fits_at_operand ok) r.1,
    fun p=>(eval_below _ _ (u.coordinateResult m) _ r.1 (u.before_setup_coordinate ok m)).trans (r.2 p)⟩

theorem public_auxiliary_rows {N : ℕ} (R : u.MeasuredChannels N) (ok : u.Ready) (m : Memory w)
    (captured : CaptureRoom R m) (j : Fin 4) :
    ((v).peerAux b j).Fits w first ∧
      Source ((v).peerAux b j) (fun (h : Fin (s).hosts) (_ : Fin (s).groups)=>
        (DescentResetPeerJointPacked.Aux.value (v).front.peer.shapes R.names R.prior R.near h j : Cell (s).metaBits))
        (s).lanes (u.beforeSetupImage ok m):=by
  let e:=(v).peerAux b j
  have fit:= (v).aux_fits b ok.packed j
  have source:=((v).joint_sources b u.earlier R.names R.now R.prior R.near (u.contactResult m)
    captured.used ok.joints captured.roster captured.three captured.distinct captured.shapes captured.keys
    captured.previousSelf ok.packed).2 j
  have privateBefore:=(v).receipt_order b
  have «meta» : (v).jointEnd b≤base:=by
    rw [←u.masks_end]
    exact privateBefore.2.trans (u.masked.ordered.1.trans u.masked.ordered.2)
  have top : base≤deck:=by rw [CandidateSheets.coordinateEnd,(s).stemSources.extent]; exact Nat.le_add_right ..
  have donors : deck≤(s).inputDonorsEnd area:=by rw [(s).donors_shift];omega
  have space:=donors.trans_lt ok.numbers.donor.room
  refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ ((v).operands_after_front b).2.1 fit,fun p=>?_⟩
  apply (eval_below e _ (u.privateStart m) _ fit (fun i hi=>
    (u.before_setup_coordinate ok m i (hi.trans_le («meta».trans top))).trans
      (u.coordinateResult_frame m ok space i hi))).trans
  have same (h : Fin (s).hosts) : (DescentResetPeerJointPacked.Aux.value (v).front.peer.shapes
      R.names R.prior R.near h j : Cell (s).metaBits)=
      ⟨_,DescentResetPeerJointPacked.Aux.value_lt _ R.names R.prior R.near h j
        captured.distinct captured.shapes captured.keys captured.previousSelf⟩ :=
    Fin.ext (Fin.val_cast_of_lt (DescentResetPeerJointPacked.Aux.value_lt _ R.names R.prior R.near h j
      captured.distinct captured.shapes captured.keys captured.previousSelf))
  simpa only [e,privateStart,contactResult,same] using source p

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
