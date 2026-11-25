import OAI.Computability.BorderVNP.CubeISALocalRowCode

/-! # Writing the physical packet-tally descriptor for a local declaration row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open Cube Cube.Tally VPVNP.BurstRAM Constants

/-- First descriptor address immediately after the sparse packet-trial reservation. -/
def metadataHead (base trials radix stride : ℕ) := base+trials*radix*stride

/-- Complete eight-word physical metadata in consecutive write order. -/
def metadataWords (n K h row head s : ℕ) : List ℕ := [
  selectorWidth n K h,Fintype.card (Selector n K h),Fintype.card (Edge (n+1)),
  row,n+1,head+8,h,s]

private theorem push_eval (src : Reg) (p : Arg → ℕ) (z : NatState) (one : z.reg 1 = 1) :
    (push src).fixedEval p z =
      ⟨Function.update z.reg 51 (z.reg 51+1),Function.update z.mem (z.reg 51) (z.reg src)⟩ := by
  simp [push,Code.block,Code.fixedEval,Code.evalNat,addressOp,one]

private theorem push_safe (src : Reg) (p : Arg → ℕ) (z : NatState) {w : ℕ}
    (one : z.reg 1 = 1) (room : z.reg 51+1 < 2^w) : (push src).fixedSafe w p z := by
  simp [push,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,addressOpFits,one,room]

private theorem lit_eval (x w : ℕ) (p : Arg → ℕ) (z : NatState)
    (one : z.reg 1 = 1) (unit : z.reg 57 = 1) (fits : x < 2^w) :
    (pushLiteral x).fixedEval p z = ⟨Function.update (Function.update z.reg 58 x) 51 (z.reg 51+1),
      Function.update z.mem (z.reg 51) x⟩ := by
  simp (config := {decide:=true}) [pushLiteral,Code.fixedEval,(literal_word_effect x w p z unit fits).2,push_eval,one]

private theorem lit_safe (x w : ℕ) (p : Arg → ℕ) (z : NatState)
    (one : z.reg 1 = 1) (unit : z.reg 57 = 1) (fits : x < 2^w) (room : z.reg 51+1 < 2^w) :
    (pushLiteral x).fixedSafe w p z := by
  obtain ⟨safe,value⟩ := literal_word_effect x w p z unit fits
  simp (config := {decide:=true}) [pushLiteral,Code.fixedSafe,value,safe,push_safe,one,room]

private theorem secondary_eval (p : Arg → ℕ) (z : NatState) :
    (CubeLengths.field 9 0).fixedEval p z =
      ⟨Function.update (Function.update (Function.update z.reg 63 0) 62 (z.mem (p 0+63)))
        9 (z.mem (z.mem (p 0+63))),z.mem⟩ := by
  simp (config := {decide:=true}) [CubeLengths.field,Code.block,Code.fixedEval,Code.evalNat,addressOp,readFrame_fixedEval]
  funext j
  by_cases h9 : j = 9 <;> by_cases h62 : j = 62 <;> by_cases h63 : j = 63 <;> simp_all

private theorem secondary_safe (p : Arg → ℕ) (z : NatState) (w : ℕ)
    (hf : p 0+63 < 2^w) (hh : z.mem (p 0+63) < 2^w) : (CubeLengths.field 9 0).fixedSafe w p z := by
  simp (config := {decide:=true}) [CubeLengths.field,Code.block,readFrame,Code.fixedSafe,Code.safeReadOnly,Code.fixedEval,
    Code.evalNat,addressOpFits,addressOp,hf,hh]
  omega

/-- The eight table entries give exactly the packet tally's checked header. -/
theorem metadataWords_header (n K h row head s : ℕ) (m : ℕ → ℕ) :
    PacketTally.Header (Constants.image head (metadataWords n K h row head s) m) head n K h row (head+8) s := by
  have field (k : Fin 8) := Constants.image_at head (metadataWords n K h row head s) m
    (⟨k.val,k.isLt⟩ : Fin (metadataWords n K h row head s).length)
  exact ⟨field 0,field 1,field 2,field 3,field 4,field 5,field 6,field 7⟩

/-- The local row's descriptor writer fetches the true H[0], issues all eight consecutive
stores, restores the descriptor and subtotal pointers, and leaves all other addresses alone.
The two actual frame reads are below the descriptor reservation. -/
theorem metadata_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (r : Bank w) (m : Memory w)
    (n K h s base trials radix stride header row : ℕ)
    (one : readings r 1 = 1) (dim : readings r 5 = n) (bits : readings r 8 = selectorWidth n K h)
    (count : readings r 9 = Fintype.card (Selector n K h)) (rad : readings r 11 = radix)
    (span : readings r 16 = stride) (bank : readings r 17 = base) (steps : readings r 19 = trials)
    (unit : readings r 57 = 1)
    (primary : readings m ((pub 0).val+63) = header) (secondary : readings m header = row)
    (primaryBefore : (pub 0).val+63 < metadataHead base trials radix stride)
    (headerBefore : header < metadataHead base trials radix stride)
    (productFit : trials*radix < 2^w)
    (room : metadataHead base trials radix stride + 8 + h < 2^w)
    (edgesFit : Fintype.card (Edge (n+1)) < 2^w) (axesFit : n+1 < 2^w) (sFit : s < 2^w) :
    let head := metadataHead base trials radix stride
    BoundedRun pub mac (metadata n h s) r m (metadata n h s).slots (fun z =>
      z.reg 8 = head ∧ z.reg 9 = row ∧ PacketTally.Header z.mem head n K h row (head+8) s ∧
      (∀ a, a < head ∨ head+8 ≤ a → z.mem a = readings m a) ∧
      (∀ j : Reg, j ∉ ([8,9,50,51,53,58,62,63] : List Reg) → z.reg j = readings r j)) := by
  intro head
  let p := readings pub
  let st := NatState.ofWords r m
  have r8 : st.reg 8 = selectorWidth n K h := bits
  have r9 : st.reg 9 = Fintype.card (Selector n K h) := count
  have r11 : st.reg 11 = radix := rad
  have r16 : st.reg 16 = stride := span
  have r17 : st.reg 17 = base := bank
  have r19 : st.reg 19 = trials := steps
  have r1 : st.reg 1 = 1 := one
  have r57 : st.reg 57 = 1 := unit
  have r5 : st.reg 5 = n := dim
  let A := p 0+63
  have hA : A < head := primaryBefore
  have hH : header < head := headerBefore
  have atA : st.mem A = header := primary
  have atH : st.mem header = row := secondary
  have hRoom : head+8+h < 2^w := room
  have space (k : ℕ) (hk : k ≤ 8) : head+k < 2^w := by omega
  have noA (k : ℕ) : A ≠ head+k := by omega
  have noH (k : ℕ) : header ≠ head+k := by omega
  have termEq : base+trials*radix*stride = head := rfl
  have mulFit : trials*radix*stride < 2^w := by omega
  have fitH : h < 2^w := by omega
  have fitA : A < 2^w := by omega
  have fitHeader : header < 2^w := by omega
  have rd (z : NatState) := secondary_eval p z
  have lv (x : ℕ) (z : NatState) := lit_eval x w p z
  have ls (x : ℕ) (z : NatState) := lit_safe x w p z
  simp at edgesFit
  have hv : 8 < 2^w := by omega
  have headFit : head < 2^w := by omega
  have belowA : A ≠ head := Nat.ne_of_lt hA
  have belowH : header ≠ head := Nat.ne_of_lt hH
  have aeq : p 0+63 = A := rfl
  have safe : (metadata n h s).fixedSafe w p st := by
    simp (config := {decide:=true,maxDischargeDepth:=20}) [metadata,beginHeader,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
      Code.evalNat,addressOpFits,addressOp,push_eval,push_safe,lv,ls,rd,secondary_safe,r1,r5,r8,r9,r11,r16,r17,r19,r57,Nat.add_assoc,
      termEq,aeq,atA,atH,belowA,belowH,noA,noH,space,headFit,productFit,mulFit,hv,fitH,fitA,fitHeader,edgesFit,axesFit,sFit]
  obtain ⟨es,t,mt,run,cost,out⟩ := (metadata n h s).runFixed pub mac r m safe
  have eval : NatState.ofWords t mt = (metadata n h s).fixedEval p st := out
  let ws := metadataWords n K h row head s
  have results : (NatState.ofWords t mt).reg 8 = head ∧ (NatState.ofWords t mt).reg 9 = row ∧
      (NatState.ofWords t mt).mem = Constants.image head ws st.mem := by
    rw [eval]
    simp (config := {decide:=true,maxDischargeDepth:=20}) [metadata,beginHeader,Code.block,Code.fixedEval,Code.evalNat,addressOp,push_eval,
      lv,rd,r1,r5,r8,r9,r11,r16,r17,r19,r57,Nat.add_assoc,termEq,aeq,atA,atH,belowA,belowH,noA,noH,fitH,edgesFit,sFit,
      ws,metadataWords,Constants.image]
  obtain ⟨out8,out9,image⟩ := results
  refine ⟨es,t,mt,run,cost,out8,out9,image ▸ metadataWords_header n K h row head s st.mem,?_,?_⟩
  · intro a ha
    rw [image]
    exact Constants.image_outside head ws _ _ ha
  · intro j hj
    have keepsLit (bs : List Bool) (hn : j ≠ 58) : (literal bs).keeps j = true := by
      induction bs with
      | nil => simpa only [literal,Code.keeps,decide_eq_true_eq] using hn
      | cons b bs ih => cases b <;> simp [literal,Code.keeps,ih,hn]
    have ne := hj
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at ne
    obtain ⟨h8,h9,h50,h51,h53,h58,h62,h63⟩ := ne
    apply congrArg Fin.val (run.keepsReg ?_)
    simp [metadata,beginHeader,Code.block,push,pushLiteral,CubeLengths.field,readFrame,Code.keeps,
      h8,h9,h50,h51,h53,h62,h63,keepsLit _ h58]

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
