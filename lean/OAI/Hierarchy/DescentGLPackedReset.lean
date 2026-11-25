import OAI.Hierarchy.DescentGLPackedBank
import OAI.Hierarchy.DescentGLPackedBlocks

namespace OAI
/-! # End-to-end CPU control, native inverse row shuffles, and packed post-reset census -/
namespace Hierarchy.DescentGLPacked.BankImage
open DescentGLPacked DescentGL DescentColonies DescentGLNielsen DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {h l H b w : ℕ}

theorem Chart.page_low (C : Chart) (i : ℕ) : C.start≤(C.pageAt i).base:=Nat.le_add_right ..

theorem static_above (C : Chart) (i : Fin (schedule (h+l)).length) (m n : Memory w)
    (original : Static (C.board i.val) (routeGate ((schedule (h+l))[i.val])) (address h) (address l) b H m)
    (frame : ∀z,C.start≤z→n z=m z) :
    Static (C.board i.val) (routeGate ((schedule (h+l))[i.val])) (address h) (address l) b H n := by
  constructor
  · intro v a;exact (frame _ ((C.page_low _).trans (Nat.le_add_right ..))).trans (original.left v a)
  · intro v a;exact (frame _ ((C.page_low _).trans (Nat.le_add_right ..))).trans (original.right v a)
  · intro v a;exact (frame _ ((C.page_low _).trans (Nat.le_add_right ..))).trans (original.family v a)
  · intro z;exact (frame _ ((C.page_low _).trans (Nat.le_add_right ..))).trans (original.shift z)
  · intro f z;exact (frame _ ((C.page_low _).trans (Nat.le_add_right ..))).trans (original.tables f z)

theorem reset {N : ℕ} (C : Chart) (sizes : Size C H h l b w)
    (T : DescentGLControlCode.Tables) (name : DescentGL.Layout (h+l) ↪ Fin N) (key : Expr)
    (L : DescentGL.Layout (h+l)) (X : Fin H→Block (h+l)→Cell b) (m : Memory w)
    (ks : DescentGLControlCode.fits T key w C.flags)
    (off : DescentGLControlCode.Count (h+l)≤T.offsets.size)
    (area : DescentGLControlCode.Count (h+l)*N≤T.switches.size)
    (stat : DescentGLControlCode.installed T name m)
    (measured : ∀i : Fin (DescentGLControlCode.Count (h+l)),key.eval m (i.val:Word w)=((name L).val:Word w))
    (source : Dense C.input.base X m) (protectedInput : C.input.base+C.input.size≤C.flags) :
    let n:=(schedule (h+l)).length
    let original:=C.install H h l b m
    let filled:=ProtocolRAM.image C.flags n (T.expr key) original
    let ps:=steps (C.chosen (h+l)) H (2^h) 0 n
    let machine:=(scan w C.flags n (T.expr key)).seq (program w ps)
    let out:=result ps filled
    machine.Exec original out ((4+n*(2*(T.expr key).work+4))+clock ps) ∧ CheapCode machine ∧
    Dense (((C.chosen (h+l)).bank n).base) (fun v z=>X v ((rearrange L).symm z)) out := by
  let n:=(schedule (h+l)).length
  let original:=C.install H h l b m
  let filled:=ProtocolRAM.image C.flags n (T.expr key) original
  let A:=C.chosen (h+l)
  let ps:=steps A H (2^h) 0 n
  have controls:C.flags+n≤C.start:=sizes.controls
  have oldFrame (i : ℕ) (small:i<C.flags) : original i=m i :=
    low_frame C H h l b m (by omega : i<C.start)
  have keep (i : ℕ) (hi:C.start≤ i) : filled i=original i := by
    simp [filled,ProtocolRAM.image,fillSegment,show ¬(C.flags≤ i ∧ i<C.flags+n) by omega]
  have row (i : Fin n) : key.eval original (i.val:Word w)=((name L).val:Word w) :=
    (eval_below _ _ m original ks.1 oldFrame).trans (measured i)
  have actual : DescentGLControlCode.installed T name original := by
    constructor
    · intro i;exact (oldFrame _ ((Nat.add_lt_add_left (i.isLt.trans_le off) _).trans_le ks.2.1.2.2)).trans (stat.1 i)
    · intro i;exact (oldFrame _ ((Nat.add_lt_add_left (i.isLt.trans_le area) _).trans_le ks.2.2.2.2)).trans (stat.2 i)
  have flags:=DescentGLControlCode.image_read T name key L C.flags ks off area original ⟨actual,row⟩
  have installed:=setup_of_read A L filled
    (fun i=>static_above C i original filled (true_tables C sizes m i) keep) flags
  have input : Reads (A.bank 0) (address h) (address l) (fun v u z=>X v (address (h+l) (Fin.append u z))) filled := by
    have raw:=(packed_iff C.input X m).1 source
    intro v u
    let pos:=(ordinal (address h) v u).val
    have below : C.input.base+pos<C.flags :=
      ((Nat.add_lt_add_left ((ordinal (address h) v u).isLt.trans_le sizes.inputSize) _).trans_le protectedInput)
    have f:filled (C.input.base+pos)=original (C.input.base+pos) := by
      simp [filled,ProtocolRAM.image,fillSegment,show ¬C.flags≤C.input.base+pos from Nat.not_le.mpr below]
    exact (f.trans (oldFrame _ below)).trans (raw v u)
  have physical:=execution A (hardware C sizes) filled 0 n (by omega)
  have chosen:=gl_read A L X filled (hardware C sizes) input installed
  have high:C.flags+n<2^w := controls.trans_lt (((C.page_low (6*n)).trans (Nat.le_add_right ..)).trans_lt sizes.top)
  have ef:(T.expr key).Fits w C.flags:=⟨ks.2.2,ks.1,ks.2.1,trivial⟩
  have issue : (scan w C.flags n (T.expr key)).Exec original filled (4+n*(2*(T.expr key).work+4)) :=
    @ProtocolRAM.scan_exec w C.flags n (T.expr key) original ef high
  exact ⟨issue.then physical.1,
    @cheap_seq w (scan w C.flags n (T.expr key)) (program w ps) (@scan_cheap w C.flags n (T.expr key)) physical.2,
    (packed_iff ..).2 chosen⟩

def chartBits (H h l b : ℕ) := max ((H*2^h).log2+1) ((b+b)*2^l)

theorem chart_room (H h l b : ℕ) :
    H*2^h≤2^chartBits H h l b ∧ 2^((b+b)*2^l)≤2^chartBits H h l b :=
  ⟨Nat.lt_log2_self.le.trans (Nat.pow_le_pow_right (by decide) (le_max_left ..)),
   Nat.pow_le_pow_right (by decide) (le_max_right ..)⟩

theorem size_of (C : Chart) (layout : C.bits=chartBits H h l b)
    (input : C.input.Fits w C.start) (inputSize : H*2^h≤C.input.size)
    (controls : C.flags+(schedule (h+l)).length≤C.start)
    (top : C.heap (h+l)+((schedule (h+l)).length+1)*C.page<2^w) : Size C H h l b w := by
  obtain ⟨rows,table⟩:=chart_room H h l b
  have cap : 2^((b+b)*2^l)≤C.page:=by simpa [Chart.page,layout] using table
  exact ⟨by simpa [Chart.page,layout] using rows,
    (Nat.pow_le_pow_right (by decide : 0<2) (Nat.mul_le_mul_right (2^l) (Nat.le_add_right b b))).trans cap,
    cap,input,inputSize,controls,top⟩

theorem footprint (H m b data cpu C : ℕ) (pos : 0<b) (wide : 4*b≤data) (scale : cpu≤C*data) :
    let l:=lowBits m b data
    2^(chartBits H (m-l) l b)*cpu ≤ C*(2^(data/2)*data+2*(H*data+8*H*2^m*b+data)) := by
  dsimp only
  let l:=lowBits m b data
  let rows:=H*2^(m-l)
  have qty:=charged H m b data data 1 pos wide (by omega)
  have count : rows*data≤H*data+8*H*2^m*b:=by simpa only [one_mul] using qty
  have small : 2^(rows.log2+1)≤2*(rows+1) := by
    rw [Nat.pow_succ]
    by_cases zero:rows=0
    · simp [zero]
    · have:=Nat.log2_self_le zero;omega
  have table:2^((b+b)*2^l)≤2^(data/2):=Nat.pow_le_pow_right (by decide) (lane_fit m b data pos wide)
  have page : 2^(chartBits H (m-l) l b)*data≤2^(data/2)*data+2*(H*data+8*H*2^m*b+data) := by
    unfold chartBits
    change 2^max (rows.log2+1) ((b+b)*2^l)*data≤_
    rcases le_total (rows.log2+1) ((b+b)*2^l) with le|le
    · rw [max_eq_right le];have:=Nat.mul_le_mul_right data table;omega
    · rw [max_eq_left le];nlinarith only [Nat.mul_le_mul_right data small,count,Nat.zero_le (2^(data/2)*data)]
  exact (Nat.mul_le_mul_left _ scale).trans (by rw [Nat.mul_left_comm];exact Nat.mul_le_mul_left C page)

end
end Hierarchy.DescentGLPacked.BankImage

end OAI
