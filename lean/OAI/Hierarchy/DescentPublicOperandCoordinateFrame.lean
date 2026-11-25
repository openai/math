import OAI.Hierarchy.DescentPhysicalPublicOriginalFrame
import OAI.Hierarchy.DescentDatedOperandMovement

namespace OAI
/-! Preservation of every coordinate word up to the actual two operand placement scans. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentPackedZip DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "s" => (v).sheets
local notation "area" => ((v).remap b).endAddress
local notation "deck" => (s).coordinateEnd area
local notation "first" => (v).operandFloor b
local notation "C" => (v).setup

theorem coordinate_before_sheets : deck≤(v).sheetsStart b := by
  have printed : deck≤(s).inputDonorsEnd area:=by rw [(s).donors_shift]; omega
  apply printed.trans
  unfold ResetOutput.sheetsStart CandidateSheets.originalEnd DescentResetOriginalSlots.finish
    CandidateSheets.original CandidateSheets.privateArgsEnd DescentUniformSlotOperands.stop
    DescentResetHaloBroadcast.endAt CandidateSheets.stemFormatEnd CandidateSheets.publicFormatEnd
    DescentResetMixedWordRAM.OriginalBooks.afterHeader CandidateSheets.donorEnd
  simp only [Nat.add_assoc]
  exact Nat.le_add_right ..

theorem sheets_entry_coordinate (ok : u.Ready) (m : Memory w) (n : ℕ) (low : n<deck) :
    u.sheetsEntry ok m n=u.coordinateResult m n:=by
  let mem:=u.masked.image (u.privateResult m)
  let pub:=(u.numbered.publicSide area).dst (u.numbered.prefixOutput area mem)
  let T:=u.numbered.stemSide area
  let A:=u.numbered.privateSide area
  let mid:=T.image pub
  let start:=(s).stemFormatEnd area
  let sg:=(s).privates
  let slots:=DescentUniformSlotOperands.result start sg (s).hosts (s).groups (s).lanes (s).argBits mid
  obtain ⟨p₁,p₂,p₃⟩:=ok.numbers.pitches
  have early : deck≤(s).inputDonorsEnd area:=by rw [(s).donors_shift]; omega
  have old : (s).privateArgsEnd area≤(s).original area:=Nat.le_add_right ..
  have finish : (s).original area≤(s).originalEnd area:=Nat.le_add_right ..
  have top : (s).originalEnd area<2^w:=ok.numbers.private_.endFits
  have stem:=(T.any ok.numbers.stem pub).2.2
  have args:=(DescentUniformSlotOperands.produce start sg (s).hosts (s).groups (s).lanes
    (s).argBits mid ok.numbers.args (old.trans_lt (finish.trans_lt top))).2.2.1
  have final:=(A.any ok.numbers.private_ slots).2.2
  have a₁:=low.trans_le (early.trans p₁)
  have a₂:=a₁.trans_le p₂
  have a₃:=a₂.trans_le p₃
  have a₄:=a₃.trans_le old
  exact (final n (.inl a₃) (fun p=>.inl (a₄.trans_le (Nat.le_add_right ..)))).trans
    ((args n (.inl a₂)).trans ((stem n (.inl a₁)).trans (u.public_original_frame ok m n low)))

theorem before_setup_coordinate (ok : u.Ready) (m : Memory w) (n : ℕ) (low : n<deck) :
    u.beforeSetupImage ok m n=u.coordinateResult m n:=by
  have earlier:=(coordinate_before_sheets (a := a) (floor := floor))
  have afterSheets : (v).sheetsStart b≤(v).candidateEnd b:=by
    rw [←ok.matched];exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have firstFit:=(v).operands_after_front b
  have hi : (C).placed first≤(v).operandStart b:=by
    apply le_trans _ ((v).keep_before b)
    change (C).placed first≤(C).endAddress first
    obtain ⟨d,e,f,g,h,i,j,k⟩:=(C).order first
    have pp:=(C).packets.join ((C).placed first)
    have a₁ : (C).placed first≤(C).packetEnd first:=pp.1.trans pp.2
    have a₂ : (C).packetEnd first≤(C).publicEnd first:=Nat.le_add_right ..
    omega
  have report:=(v).sheets_to_packet u.sectors ((v).sheetsStart b) b u.degree u.bank (u.sheetsEntry ok m)
    ok.matched ok.full ok.header ok.original ok.rows ok.width ok.rankPorts ok.ranks ok.controls ok.placed
  have src:=(C).sources_run first (u.beforeSetupImage ok m) u.bank ok.placed
    ((hi.trans firstFit.2.2.2.2).trans_lt ok.full)
  have old:=low.trans_le earlier
  have low₁:=old.trans_le (afterSheets.trans firstFit.2.2.2.1)
  exact (src.frame n (.inl low₁)).symm.trans ((report.frame n (.inl old)).trans (u.sheets_entry_coordinate ok m n low))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
