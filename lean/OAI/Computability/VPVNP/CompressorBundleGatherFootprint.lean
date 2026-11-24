import OAI.Computability.VPVNP.CompressorBundleFixedGatherTable
import OAI.Computability.VPVNP.CompressorSlotScanFootprint
import OAI.Computability.VPVNP.CompressorLogAccess

/-! # Physical addresses of the fixed shrinking key gather

Each cursor reads one initialized ID slot, follows that actual ID to a
classifier key and writes exactly the corresponding gathered-key slot.
Unused padding in the ID rectangle has no effect on the footprint.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleGather.Fixed

open BurstRAM PrimedStackRAM SourceTransport BundleKeys
open private live from OAI.Computability.VPVNP.CompressorBundleFixedGatherTable

variable {w : ℕ}

theorem table_access (t : KeyTable w) (reg : t.Layout) (fit : entryCount t < 2^w) (init : Memory w)
    (legal : ∀ b < 2*t.bundles, ∀ i < t.rowSize b, (init (t.idStart b+i)).val < t.arcCount)
    (rs : List (Report w)) (hr : runSegment ((template visit 0).instantiate w (parameters t)).program 29
      (some 0) init (List.replicate (entryCount t) []) = some rs) :
    LogAccess (fun x ↦ t.idsBase.val ≤ x ∧ x < t.idsBase.val+slots t ∨
      t.keyBase.val ≤ x ∧ x < t.keyBase.val+t.arcCount)
      (fun x ↦ t.outputBase.val ≤ x ∧ x < t.outputBase.val+slots t) rs := by
  let p := parameters t
  let I (mem : Memory w) := ∀ j : Fin (entryCount t), mem (t.idsBase.val+(slot t reg j).val) =
    init (t.idsBase.val+(slot t reg j).val)
  apply SlotEventBounds.scan _ 29 (entryCount t) (events p) I _ _ (native p) _ init rs (fun _ ↦ rfl) hr
  intro j hj mem keep
  let x : Fin (entryCount t) := ⟨j,hj⟩
  let i := word (w := w) j
  let off := offset p i
  have hoff : off.val = (slot t reg x).val := offset_eq t reg fit x
  have hext : slots t = 2*t.bundles*t.stride := by rw [slots,two_mul]
  have ho : off.val < slots t := hoff ▸ (slot t reg x).isLt
  have idsFit : t.idsBase.val+(2*t.bundles)*t.stride ≤ 2^w := reg.idsFit
  have outFit : t.outputBase.val+(2*t.bundles)*t.stride ≤ 2^w := reg.outputFits
  have src : (p 4+off).val = t.idsBase.val+(slot t reg x).val := by
    change (t.idsBase+off).val = _
    rw [Fin.val_add,hoff,Nat.mod_eq_of_lt (by have := (slot t reg x).isLt; omega)]
  have dst : (p 6+off).val = t.outputBase.val+off.val := by
    change (t.outputBase+off).val = _
    rw [Fin.val_add,Nat.mod_eq_of_lt (by omega)]
  let id := mem (p 4+off).val
  have hid : id.val < t.arcCount := by
    change (mem (p 4+off).val).val < _
    rw [src,keep x]
    obtain ⟨b,z,hb,hz,eq⟩ := live t reg x
    rw [eq,← Nat.add_assoc]; exact legal b hb z hz
  have key : (p 5+id).val = t.keyBase.val+id.val := by
    change (t.keyBase+id).val = _
    rw [Fin.val_add,Nat.mod_eq_of_lt (by have := reg.keysFit; omega)]
  have read : Reads (fun z ↦ t.idsBase.val ≤ z ∧ z < t.idsBase.val+slots t ∨
      t.keyBase.val ≤ z ∧ z < t.keyBase.val+t.arcCount) (events p mem i) := by
    intro addr value h
    simp only [events,List.mem_append,List.mem_replicate,List.mem_cons,List.not_mem_nil,
      reduceCtorEq,Event.read.injEq,and_false,or_false,false_or] at h
    rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · left; rw [src]; exact ⟨Nat.le_add_right ..,Nat.add_lt_add_left (slot t reg x).isLt _⟩
    · right; rw [key]; exact ⟨Nat.le_add_right ..,Nat.add_lt_add_left hid _⟩
  have write : Writes (fun z ↦ t.outputBase.val ≤ z ∧ z < t.outputBase.val+slots t) (events p mem i) := by
    intro addr value h
    simp only [events,List.mem_append,List.mem_replicate,List.mem_cons,List.not_mem_nil,
      reduceCtorEq,Event.write.injEq,and_false,or_false,false_or] at h
    obtain ⟨rfl,_⟩ := h
    rw [dst]; exact ⟨Nat.le_add_right ..,Nat.add_lt_add_left ho _⟩
  refine ⟨read,write,fun k ↦ (SourceTransport.after_outside mem write ?_).trans (keep k)⟩
  have apart : t.idsBase.val+(2*t.bundles)*t.stride ≤ t.outputBase.val ∨
      t.outputBase.val+(2*t.bundles)*t.stride ≤ t.idsBase.val := reg.idsApart
  have := (slot t reg k).isLt
  omega

end CompressorRecords.BundleGather.Fixed

end VPVNP
end Computability
end OAI
