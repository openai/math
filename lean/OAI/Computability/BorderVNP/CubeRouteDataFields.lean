import OAI.Computability.BorderVNP.CubeRouteDataLayouts
import OAI.Computability.BorderVNP.CubeISALocalRowGroupLayout

/-! # Public fields for the cell-bank and pair writers at the checked group return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open BorderVNP.Cube LocalRow VPVNP.BurstRAM CubeHeaderInstall

/-- The checked scheduler supplies the selected coordinate and divisor, labels,
cell count, group count and owner array. The two output pointers and the three
control-directory words are the other reads of the following native writers. -/
theorem Layout.writer_fields (a : Layout) (frame controls : ℕ) (axis : Fin (a.n+1))
    {R w X : ℕ} {orig scheduled : ℕ → ℕ}
    (checked : GroupWeights.CheckedFrame (weightLayout a frame axis.val) (teamLayout a R) orig w X)
    (out : GroupWeights.ScheduleResult (weightLayout a frame axis.val) (teamLayout a R) orig scheduled)
    (frameLow : frame+112 ≤ a.header.header)
    (host : scheduled (frame+72)=a.hostDirectory) (pair : scheduled (frame+91)=a.pairDirectory)
    (controlsAt : scheduled (frame+92)=controls) (banks : scheduled (controls+9)=a.cellBank)
    (stride : scheduled (controls+10)=a.cellStride) :
    (a.cellWriter frame controls axis).Fields scheduled ∧ (a.pairWriter frame).Fields scheduled := by
  obtain ⟨head,_,_,_,_,_,_,_⟩ := a.writer_order
  obtain ⟨_,_,_,_,_,_,pw,gw,gt,tot,_⟩ := a.group_order
  have keep (x : ℕ) (hx : x < a.groupWeights) : scheduled x = orig x := by
    apply out.other
    · change ∀ j < a.header.d, x ≠ a.groupWeights+j; omega
    · change ∀ j : Fin (R+1), x ≠ a.teamTotals+j.val; omega
    · change ∀ j < a.header.d, x ≠ a.ownerBase+j; omega
  have primary (k : ℕ) (hk : k < 112) := keep (frame+k) (by omega)
  have secondary (k : ℕ) (hk : k < 13) := keep (a.header.header+k) (by omega)
  have power := keep (a.powerBase+axis.val) (by have := axis.isLt; omega)
  have f := checked.fields
  constructor
  · exact ⟨(primary 11 (by decide)).trans f.cells,(primary 74 (by decide)).trans checked.frame.groupCount,
      (primary 48 (by decide)).trans f.labels,(primary 77 (by decide)).trans checked.frame.ownerBase,host,
      (primary 62 (by decide)).trans f.powers,(primary 63 (by decide)).trans f.header,controlsAt,
      (secondary 5 (by decide)).trans f.axis,power.trans f.place,banks,stride⟩
  · exact ⟨(primary 56 (by decide)).trans f.alphabet,(primary 59 (by decide)).trans f.groups,
      (primary 60 (by decide)).trans f.axes,(primary 63 (by decide)).trans f.header,
      (secondary 7 (by decide)).trans f.blocks,pair⟩

/-- Read the destination and pair-directory pointers from the actual 81-word boot
extension. The genuine geometry return supplies the controls pointer and the two
fixed cell-bank words in the lower region before the group prefix starts. -/
theorem Layout.writer_fields_from_boot {w : ℕ} (a : Layout) (pub : Arg → Word w) (f : BroadcastFrame)
    (old : Fin 81 → Word w) (fresh profile gates outputs width off ell : ℕ)
    {bits : List Bool} {entry : Memory w}
    (pins : BootPins pub f (jointFields (a.extension old) fresh profile gates outputs width off ell
      a.header.d a.n a.header.blocks a.b a.h a.s) bits entry)
    (controls : ℕ) (axis : Fin (a.n+1)) {R X : ℕ} {orig scheduled : ℕ → ℕ}
    (checked : GroupWeights.CheckedFrame (weightLayout a (pub 0).val axis.val) (teamLayout a R) orig w X)
    (out : GroupWeights.ScheduleResult (weightLayout a (pub 0).val axis.val) (teamLayout a R) orig scheduled)
    (frameLow : (pub 0).val+112 ≤ a.header.header) (ctrlLow : controls+10 < a.header.header)
    (room : a.stop < 2^w) (kept : ∀ x < a.header.header, scheduled x = readings entry x)
    (controlsAt : readings entry ((pub 0).val+92)=controls)
    (banks : readings entry (controls+9)=a.cellBank) (stride : readings entry (controls+10)=a.cellStride) :
    (a.cellWriter (pub 0).val controls axis).Fields scheduled ∧ (a.pairWriter (pub 0).val).Fields scheduled := by
  obtain ⟨_,_,_,_,ph,hr,rp,ps⟩ := a.writer_order
  have hostFit : a.hostDirectory < 2^w := by omega
  have pairFit : a.pairDirectory < 2^w := by omega
  exact a.writer_fields (pub 0).val controls axis checked out frameLow
    ((kept _ (by omega)).trans (pins.arenaOperand a old fresh profile gates outputs width off ell rfl hostFit))
    ((kept _ (by omega)).trans (pins.arenaOperand a old fresh profile gates outputs width off ell rfl pairFit))
    ((kept _ (by omega)).trans controlsAt) ((kept _ (by omega)).trans banks) ((kept _ ctrlLow).trans stride)

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
