import OAI.Hierarchy.DescentPhysicalOriginalScalarFrame
import OAI.Hierarchy.DescentCapturedRankChannels
import OAI.Hierarchy.DescentResetOriginalJointDigits

namespace OAI
/-! # The numbered reset digits on the actual post-coordinate memory of the date -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSixParty.Chronology DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)

def originalNumberBase (a : PhysicalReset) (floor : ℕ) :=
  a.successor.sheets.coordinateEnd ((a.successor.remap (a.rebased floor)).endAddress)

def originalScalarBank (a : PhysicalReset) (floor : ℕ) (j : Fin 4) : Bank :=
  let v:=a.successor
  let s:=v.sheets
  DescentResetPeerJointPacked.Aux.bank
    (DescentResetPeerJointPacked.endAddress (v.massEnd (a.rebased floor)) s.hosts v.front.peer.hosts s.groups s.lanes s.metaBits)
    s.hosts j

def originalNumberPhase (a : PhysicalReset) (floor w : ℕ) : NativePhase w :=
  let s:=a.successor.sheets
  DescentResetOriginalZeroHalo.phase w (originalNumberBase a floor) s.hosts s.groups s.lanes s.metaBits
    s.zeroBits s.shortBits s.haloBits a.successor.front.peer.oldDegree

theorem original_numbers {N : ℕ} (R : u.MeasuredChannels N) (m : Memory w) (ok : u.Ready)
    (seen : CaptureRoom R m)
    (room : a.successor.sheets.inputDonorsBase ((a.successor.remap (a.rebased floor)).endAddress)<2^w) :
    let s:=a.successor.sheets
    let p:=a.successor.front.peer
    let start:=originalNumberBase a floor
    let input:=u.coordinateResult m
    let pgm:=originalNumberPhase a floor w
    let value:=fun (j : Fin 4) (h : Fin s.hosts)=> (⟨DescentResetPeerJointPacked.Aux.value p.shapes R.names R.prior R.near h j,
      DescentResetPeerJointPacked.Aux.value_lt p.shapes R.names R.prior R.near h j seen.distinct seen.shapes
        seen.keys seen.previousSelf⟩ : Cell s.metaBits)
    pgm.Runs input ∧ DescentResetOriginalZeroHalo.Sources start s.hosts s.groups s.lanes s.metaBits
      s.zeroBits s.shortBits s.haloBits p.oldDegree (originalScalarBank a floor 0)
      (originalScalarBank a floor 1) (value 0) (value 1) (pgm.image input) ∧
    ∀i,i<start ∨ s.inputDonorsBase ((a.successor.remap (a.rebased floor)).endAddress) ≤ i →
      pgm.image input i=input i := by
  intro s p start input pgm value
  let v:=a.successor
  let b:=a.rebased floor
  let r:=(v.remap b).endAddress
  have bound : start ≤ s.inputDonorsBase r := (Nat.le_add_right ..).trans
    (DescentResetOriginalZeroHalo.written_le start s.hosts s.groups s.lanes s.metaBits)
  have order : v.jointEnd b ≤ start := by
    have cut:=v.privateShape.cuts (v.jointEnd b)
    have before : v.jointEnd b ≤ u.masked.first:=cut.1.trans cut.2
    have rows : v.jointEnd b ≤ s.metaEnd r:=by
      rw [←u.masks_end];exact before.trans (u.masked.ordered.1.trans u.masked.ordered.2)
    have extra : s.metaEnd r ≤ s.coordinateEnd r:=by
      rw [CandidateSheets.coordinateEnd,s.stemSources.extent]
      exact Nat.le_add_right ..
    exact rows.trans extra
  have span : 3*p.hosts ≤ (v.initialPeers b).size:=
    (by omega : 3*p.hosts ≤ p.hosts*4).trans (Nat.le_pow_clog (by decide) _)
  exact DescentResetOriginalZeroHalo.run_joint (v.massEnd b) start p.shapes s.zeroBits s.shortBits s.haloBits
    (v.jointRegisters b u.earlier) (v.initialPeers b) R.names R.now R.prior R.near (u.contactResult m) input
    seen.used ok.joints.measured ok.joints.original span seen.roster seen.three seen.distinct seen.shapes
    seen.keys seen.previousSelf order (u.coordinateResult_frame m ok (bound.trans_lt room)) room

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
