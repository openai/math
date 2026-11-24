import OAI.Computability.VPVNP.LiveHeaderComplete
import OAI.Computability.VPVNP.LiveHeaderPrefixReject

/-!
# Rejection of malformed padding by the complete native header table

The deterministic prefix from the physical processor headers reaches the
first malformed padding interval with its actual offset and count. Every
continuing padding report leaves the linker's tag intact. Any accepting
header path would therefore complete that scan, contradicting its guard.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule LiveHeaderDescriptors
open LiveHeader ChainAssignments

variable {w d : ℕ}

/-- Arbitrary branch lists and all enclosing fuel bounds above the fixed
instruction budget fail on malformed incident padding. -/
theorem bad_padding_native (s : Sizes) (base cap : ℕ) (hw : 4 ≤ w) (advice : CutSchedule.Bits s.advice)
    (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) (tag : Mode.Tag)
    (bounds : Fields.Bounds s base d w) (indices : s.h+2 ≤ 2^d) (adv : s.advice ≤ 2^d)
    (tagFit : stages.length ≤ 2^w) (fuel : 107 ≤ cap)
    (hsel : physicalTag cuts g = some tag) (bad : ¬ ∀ side, Fields.ValidPadding s cuts g tag side) :
    let P := (program.instantiate w (publicData w s base)).program
    let m := physicalMemory (d := d) hw advice cuts g
    ¬ ∃ bs rs, runSegment P cap (some 0) m bs = some rs ∧ endState (some 0) rs = none := by
  let m := physicalMemory (d := d) hw advice cuts g
  obtain ⟨xs,mid,pre,firstGood,ready⟩ := prepared_prefix s base hw advice cuts g tag hsel indices adv
    bounds.scratch bounds.fit.le
  obtain ⟨side,id,ys,atScan,hid,restGood,rest,rejected⟩ := Fields.bad_prefix bounds ready.sources bad
  have full := pre.append rest
  have allGood (x : StageTrace w) (hx : x ∈ xs++ys) := (List.mem_append.mp hx).elim (firstGood x) (restGood x)
  have hbase : (Fin.ofNat (2^w) base).val = base := by
    have ht := bounds.fit
    rw [limit_eq] at ht
    exact Nat.mod_eq_of_lt (by omega)
  have hz : m (Fin.ofNat (2^w) base).val = 0 := by
    simp only [m,physicalMemory,RAMMemory.initialMemory,hbase,ite_eq_right bounds.scratch.not_gt]
  apply full.rejects allGood tagFit (by simpa only [stage_count] using fuel) (by rintro i ⟨⟩; exact hz) rejected
  intro f st mem b r run _
  unfold nativeStage at run
  rw [hid] at run
  exact ScanRows.padding_call_frame s base side f st mem b run _ mem

/-- Under an agreed mode, the complete header accepts exactly when the
two actual cuts are canonically padded. -/
theorem native_padding_iff (s : Sizes) (base cap : ℕ) (hw : 4 ≤ w) (advice : CutSchedule.Bits s.advice)
    (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) (tag : Mode.Tag)
    (bounds : Fields.Bounds s base d w) (indices : s.h+2 ≤ 2^d) (adv : s.advice ≤ 2^d)
    (tagFit : stages.length ≤ 2^w) (fuel : 107 ≤ cap) (hsel : physicalTag cuts g = some tag) :
    let P := (program.instantiate w (publicData w s base)).program
    let m := physicalMemory (d := d) hw advice cuts g
    (∃ bs rs, runSegment P cap (some 0) m bs = some rs ∧ endState (some 0) rs = none) ↔
      ∀ side, Fields.ValidPadding s cuts g tag side := by
  constructor
  · intro accept
    by_contra bad
    exact bad_padding_native s base cap hw advice cuts g tag bounds indices adv tagFit fuel hsel bad accept
  · intro valid
    obtain ⟨rs,run,last,_⟩ := valid_native s base cap hw advice cuts g tag bounds indices adv tagFit fuel hsel valid
    exact ⟨_,rs,run,last⟩

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
