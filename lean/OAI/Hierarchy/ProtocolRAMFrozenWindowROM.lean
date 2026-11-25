import OAI.Hierarchy.ProtocolRAMFrozenWindowRun
import OAI.Hierarchy.ProtocolRAMPackedROM

namespace OAI
/-! # The fixed public lookup words for an allocated format -/
noncomputable section
namespace Hierarchy.ProtocolRAMFrozenWindow
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open ProtocolRAM ProtocolRAMReportedPorts TaggedShorterReportAdvice
open scoped Classical Fin.CommRing

variable {W : ℕ}

def Format.biasBase (f : Format) := f.rom+13*2^f.bits
def Format.originBase (f : Format) := f.biasBase+2^f.gb
def Format.adviceEnd (f : Format) := f.originBase+2^f.gb

def Format.publicInputs (f : Format) (inputs : Inputs) : Inputs :=
  { inputs with
    classes := bank f.rom f.bits 3
    weights := bank f.rom f.bits 4
    bias := ⟨f.biasBase, f.gb⟩
    origins := ⟨f.originBase, f.gb⟩ }

/-- The thirteen arithmetic and routing tables, the weighted-counter bias and the
raw-width destination pointer are independent of all reported widths and decisions. -/
def Format.mount (f : Format) (r : ℕ) (m : Memory W) : Memory W :=
  let selectors:=store f.rom f.bits (words f.groups f.D f.B f.M (f.window.base r) f.w f.menu f.cap) m
  let bias:=fillSegment f.biasBase (2^f.gb) (fun x=>((x-f.biasBase)*(f.menu+1):ℕ)) selectors
  TaggedShorterSlotWidth.originStore f.originBase f.groups (f.window.widthBase r) f.D bias

theorem Format.mount_frame (f : Format) (r : ℕ) (m : Memory W) (groupsFit : f.groups≤2^f.gb) (x : ℕ)
    (free : x<f.rom ∨ f.adviceEnd≤x) : f.mount r m x=m x := by
  unfold Format.adviceEnd Format.originBase Format.biasBase at free
  have origin : x<f.originBase ∨ f.originBase+f.groups≤x := by
    unfold Format.originBase Format.biasBase;omega
  have bias : ¬(f.biasBase≤x ∧ x<f.biasBase+2^f.gb) := by unfold Format.biasBase;omega
  have page : ¬(f.rom≤x ∧ x<f.rom+13*2^f.bits) := by omega
  simp only [Format.mount,TaggedShorterSlotWidth.originStore_frame _ _ _ _ _ _ origin,fillSegment,ite_eq_right bias,
    store,ite_eq_right page]

theorem Format.input_words (f : Format) (r : ℕ) (inputs : Inputs) (m before : Memory W)
    (old : Fin f.N→ProtocolRAMEmit.Row) (limits : f.Limits W old)
    (retained : ∀x,f.rom≤x → x<f.adviceEnd → m x=f.mount r before x)
    (width : ∀i : Fin f.N,inputs.width.read m ((3*i.val:ℕ):Word W)=((old i).width:Word W)) :
    f.InputWords r (f.publicInputs inputs) old m := by
  let page:=store f.rom f.bits (words f.groups f.D f.B f.M (f.window.base r) f.w f.menu f.cap) before
  let biased:=fillSegment f.biasBase (2^f.gb) (fun x=>(((x-f.biasBase)*(f.menu+1):ℕ):Word W)) page
  have biasBeforeOrigin : f.biasBase ≤ f.originBase := Nat.le_add_right ..
  have originBeforeEnd : f.originBase ≤ f.adviceEnd := Nat.le_add_right ..
  have table (j : Fin 13) (x : ℕ) (small : x<2^f.bits) :
      (bank f.rom f.bits j).read m (x:Word W)=words f.groups f.D f.B f.M (f.window.base r) f.w f.menu f.cap j x := by
    have wide:=small.trans_le limits.wide
    have endCol:=Nat.mul_le_mul_right (2^f.bits) j.isLt
    rw [Nat.succ_mul] at endCol
    have high : f.rom+j.val*2^f.bits+x<f.biasBase := by unfold Format.biasBase;omega
    have aeq:=read_store f.rom f.bits (words f.groups f.D f.B f.M (f.window.base r) f.w f.menu f.cap) before j x small wide
    change page (f.rom+j.val*2^f.bits+(x:Word W).val%2^f.bits)=_ at aeq
    change m (f.rom+j.val*2^f.bits+(x:Word W).val%2^f.bits)=_
    simp only [Fin.val_cast_of_lt wide,Nat.mod_eq_of_lt small] at aeq ⊢
    rw [retained _ (by omega) (high.trans_le (biasBeforeOrigin.trans originBeforeEnd))]
    change TaggedShorterSlotWidth.originStore _ _ _ _ biased _=_
    rw [TaggedShorterSlotWidth.originStore_frame _ _ _ _ _ _ (Or.inl (high.trans_le biasBeforeOrigin))]
    change fillSegment _ _ _ page _=_
    rw [fillSegment,ite_eq_right (by omega)]
    exact aeq
  have typed:=ProtocolRAMPackedRanked.report_rom old m table limits.widthFit
  refine ⟨width,?_,typed.1,typed.2,table,?_⟩
  · intro t
    let j:=t.val%2^f.gb
    have lt : j<2^f.gb := Nat.mod_lt _ (Nat.two_pow_pos _)
    change m (f.biasBase+j)=_
    rw [retained _ (by unfold Format.biasBase;omega) (by unfold Format.adviceEnd Format.originBase;omega)]
    have low : f.biasBase+j<f.originBase := by unfold Format.originBase;omega
    change TaggedShorterSlotWidth.originStore _ _ _ _ biased _=_
    rw [TaggedShorterSlotWidth.originStore_frame _ _ _ _ _ _ (Or.inl low)]
    change fillSegment f.biasBase (2^f.gb) _ page _=_
    simp [fillSegment,lt,j]
  · intro g
    have gw:=g.isLt.trans_le (limits.groups.trans limits.groupWords)
    have fitted:=g.isLt.trans_le limits.groups
    change m (f.originBase+(g.val:Word W).val%2^f.gb)=_
    rw [Fin.val_cast_of_lt gw,Nat.mod_eq_of_lt fitted,
      retained _ (by unfold Format.originBase Format.biasBase;omega) (by unfold Format.adviceEnd;omega)]
    have val:=TaggedShorterSlotWidth.originStore_read f.originBase f.gb (f.window.widthBase r) f.D biased
      limits.groups (limits.groups.trans limits.groupWords) g
    change f.mount r before (f.originBase+(g.val:Word W).val%2^f.gb)=_ at val
    simpa only [Fin.val_cast_of_lt gw,Nat.mod_eq_of_lt fitted] using val

end Hierarchy.ProtocolRAMFrozenWindow
end

end OAI
