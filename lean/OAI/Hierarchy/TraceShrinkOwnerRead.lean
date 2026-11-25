import OAI.ThreeFlat.Diagonal.PhysicalShrinkOutputData
import OAI.ThreeFlat.Diagonal.ShrinkPublishedChildren

namespace OAI
/-! # Owner pointers in the output of the native shrink writer -/

namespace Hierarchy.TraceShrinkRetained

open ThreeFlat Diagonal Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident Native.ShrinkStage.DescriptorSpan Native.Placement Native.Graph
open NavigationDirectory NavigationPass PhysicalShrink ShrinkStageNav
open scoped Classical BigOperators Fin.NatCast
noncomputable section
variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
set_option quotPrecheck false
local notation "M" => shrinkBinary T s D rem hD small A
local notation "B" => shrinkRecordState s rem A
local notation "N" => Fintype.card (B).Base
local notation "P" => shrinkRecordPacking s rem A
local notation "d" => (2^s:ℕ)
local notation "k" => (2*d+1:ℕ)
local notation "hc" => (show 2≤k from by have:=Nat.two_pow_pos s;omega)
local notation "S" => shrinkStage s D
local notation "t" => CompressorPacking.tagBits d
local notation "x" => dims S N t rem
local notation "prior" => shrinkRecordWidth s rem A
local notation "supply" => shrinkIssuedWords T s D rem hD small A

private theorem owner_range (alphabet : ℕ) (cursor : Cursor) (shape : Dimensions) :
    let entry := allocate alphabet cursor (.shrink shape)
    cursor.heap ≤ entry.words 44 ∧ entry.words 44+shape.originalSites=entry.next.heap ∧
      shape.outputSites ≤ entry.next.heap := by
  simp [allocate,headerExtra,extraEnd]; omega

/-- Read the old-site indexed owner column of this invocation. -/
theorem owner {K W : ℕ} (cur : Word W) (m out : Memory W) (c : Cursor)
    (branch : Fin (M).rules.count) (H : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (old : ShrinkOldCaps s rem W) (a : ChildRows.Actual P) :
    let en := allocate K c (.shrink x)
    let read := en.words 44+ChildRows.oldNumber P (B).order a
    (out read).val=Incidents.siteNumber (B).order ((P).placement (ShrinkMotif.chooseWidths (supply branch)) a) ∧
      c.heap≤read ∧ read<en.next.heap := by
  let E:=shrinkOutputCodec s rem A old
  have le : s≤W := ((Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp old.slots).le
  have chart (z : BitWord s) : slotCode (w:=W) P z=tagWord le z := Demand.tag_cast le z
  have add (a b : BitWord s) : slotCode (w:=W) P (a+b)=BinaryOp.bitXor.eval (slotCode P a) (slotCode P b) := by
    simpa only [chart] using tagWord_add le a b
  have sub (a b : BitWord s) : slotCode (w:=W) P (a-b)=BinaryOp.bitXor.eval (slotCode P a) (slotCode P b) := by
    simpa only [chart] using tagWord_sub le a b
  let en:=allocate K c (.shrink x)
  have range : c.heap≤en.words 44 ∧ en.words 44+(x).originalSites=en.next.heap ∧ (x).outputSites≤en.next.heap := by
    exact owner_range K c x
  have room:=H.cursor.controls.trans_lt cur.isLt
  let lay:=ShrinkMotif.chooseWidths (supply branch)
  have num : Incidents.siteNumber (B).order ((P).placement lay a)<(x).outputSites := DescriptorSpan.site_number_lt (b:=(B).order) _
  have reach : ChildRows.oldNumber P (B).order a<(x).originalSites := ChildRows.oldNumber_lt P (B).order a
  have outWord:=PublishedDescriptors.owner_word (S₀:=S) (q:=2*d) («P» := P) (b := (B).order)
    (raw := m) (final := out) (kind := 1) H.records H.cursor H.descHeader H.descInput E
    (fun _=>rfl) add sub old.colors old.slots a
  change out (en.words 44+ChildRows.oldNumber P (B).order a)=(Incidents.siteNumber (B).order ((P).placement lay a):Word W) at outWord
  change (out (en.words 44+ChildRows.oldNumber P (B).order a)).val=_ ∧ _ ∧ _
  rw [outWord,Fin.val_cast_of_lt ((num.trans_le range.2.2).trans room)]
  exact ⟨rfl,range.1.trans (Nat.le_add_right _ _),
    (Nat.add_lt_add_left reach (en.words 44)).trans_eq range.2.1⟩


end
end Hierarchy.TraceShrinkRetained

end OAI
