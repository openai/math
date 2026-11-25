import OAI.Optimization.LinearProgramming.Compression.PowerTapeEncoder
import OAI.Optimization.LinearProgramming.RAM.Array
import Mathlib.Tactic

/-! Install the canonical signed-binary address header directly before a token stream.
The stream is left in place; only its prefix and explicit scratch registers are written. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private inductive IndexOp where
  | set (dst value : ℕ)
  | copy (dst src : ℕ)
  | inc (dst : ℕ)

private def IndexOp.dst : IndexOp → ℕ
  | .set r _ | .copy r _ | .inc r => r

private def IndexOp.instr : IndexOp → Instr
  | .set r v => .addrConst r v
  | .copy r s => .addrCopy r s
  | .inc r => .incr r r

private def IndexOp.value (op : IndexOp) (f : ℕ → ℕ) : ℕ :=
  match op with
  | .set _ v => v
  | .copy _ s => f s
  | .inc r => f r+1

private def indicesAfter (is : List IndexOp) (f : ℕ → ℕ) : ℕ → ℕ :=
  is.foldl (fun g op => Function.update g op.dst (op.value g)) f

private def indexOps (is : List IndexOp) := Block.straight (is.map IndexOp.instr)

private theorem indexOps_eval (is : List IndexOp) (m : Memory K) {P : K → Prop} (hm : m.AllData P) :
    Block.Eval (Memory.AllData P) (indexOps is) m is.length ⟨m.data,indicesAfter is m.index⟩ := by
  induction is generalizing m with
  | nil => exact .skip hm
  | cons i is ih =>
    let s := m.putIndex i.dst (i.value m.index)
    have one : Block.Eval (Memory.AllData P) (.op i.instr) m 1 s := by
      cases i with
      | set r v => exact Block.Eval.op_addrConst m r v hm hm
      | copy r a => exact Block.Eval.op_addrCopy m r a hm hm
      | inc r => exact Block.Eval.op_incr m r r hm hm
    simpa [indexOps,indicesAfter,s,Memory.putIndex,Block.straight,Nat.add_comm] using one.seq (ih s hm)

private theorem indexOps_frame (is : List IndexOp) (f : ℕ → ℕ) (j : ℕ)
    (h : ∀ i ∈ is, i.dst ≠ j) : indicesAfter is f j = f j := by
  induction is generalizing f with
  | nil => rfl
  | cons i is ih =>
    change indicesAfter is _ j = _
    rw [ih _ (fun i' hi' => h i' (by simp [hi']))]
    exact Function.update_of_ne (h i (by simp)).symm _ _

private def pushAddressWords : List ℕ → Block
  | [] => .skip
  | r::rs => .seq (.op (.decr 57 57)) (.seq (.op (.addrStore 57 r)) (pushAddressWords rs))

private theorem pushAddressWords_spec (rs : List ℕ) (m : Memory K) (top : ℕ) {P : K → Prop}
    (hm : m.AllData P) (hptr : m.index 57 = top) (hroom : 64+rs.length ≤ top)
    (regs : ∀ r ∈ rs, r < 64 ∧ r ≠ 57) :
    ∃ s, Block.Eval (Memory.AllData P) (pushAddressWords rs) m (2*rs.length) s ∧
      s.data = m.data ∧ s.index 57 = top-rs.length ∧
      (∀ j, ∀ hj : j < rs.length, s.index (top-1-j) = m.index rs[j]) ∧
      ∀ i, i ≠ 57 → (i < top-rs.length ∨ top ≤ i) → s.index i = m.index i := by
  induction rs generalizing m top with
  | nil => exact ⟨m,.skip hm,rfl,by simpa using hptr,by simp,fun _ _ _ => rfl⟩
  | cons r rs ih =>
    have hreg := regs r (by simp)
    let a := m.putIndex 57 (top-1)
    let b := a.putIndex (top-1) (m.index r)
    have ea : Block.Eval (Memory.AllData P) (.op (.decr 57 57)) m 1 a := by
      simpa only [a,hptr] using Block.Eval.op_decr (safe := Memory.AllData P) m 57 57 hm hm
    have eb : Block.Eval (Memory.AllData P) (.op (.addrStore 57 r)) a 1 b := by
      simpa [b,a,hreg.2] using Block.Eval.op_addrStore (safe := Memory.AllData P) a 57 r hm hm
    have htop : b.index 57 = top-1 := by
      simp only [List.length_cons] at hroom
      simp [a,b,show 57 ≠ top-1 by omega]
    have eqold (i : ℕ) (h57 : i ≠ 57) (hpos : i ≠ top-1) : b.index i = m.index i := by
      simp [a,b,h57,hpos]
    obtain ⟨s,run,sd,sp,words,frame⟩ := ih b (top-1) hm htop
      (by simp only [List.length_cons] at hroom;omega) (fun j hj => regs j (by simp [hj]))
    refine ⟨s,?_,sd,?_,?_,?_⟩
    · convert ea.seq (eb.seq run) using 1 <;> first | rfl | omega | (simp only [List.length_cons];omega)
    · simp only [List.length_cons];omega
    · intro j hj
      cases j with
      | zero =>
        rw [Nat.sub_zero,frame (top-1) (by simp only [List.length_cons] at hroom;omega) (Or.inr le_rfl)]
        simp [b]
      | succ j =>
        have hj' : j < rs.length := by simpa using hj
        have hword := words j hj'
        have hr := regs rs[j] (by simp [List.getElem_mem hj'])
        have hg : top-1-(j+1) = top-1-1-j := by omega
        simpa only [hg,List.getElem_cons_succ, eqold _ hr.2
          (by simp only [List.length_cons] at hroom; omega)] using hword
    · intro i hi hf
      simp only [List.length_cons] at hf
      exact (frame _ hi (by omega)).trans (eqold _ hi (by omega))

private def padSetup : List IndexOp :=
  [.copy 57 59, .copy 6 59, .set 7 8, .set 58 8, .set 8 0, .set 9 1,
   .set 10 2, .set 11 3, .set 12 4, .set 13 8]

private def padBumps : List IndexOp := [.inc 7,.inc 7,.inc 58,.inc 58,.inc 58,.inc 6]

private def padBody : Block := .seq (pushAddressWords [8,8]) (indexOps padBumps)

private def headerSources : List ℕ := [12,11,10,9,8,13,58,7]

/-- Address 59 is the first literal token, 34 the next free token. The routine
writes backward into reserved space, leaves tokens untouched, and returns the
staged array base and length in address registers 57 and 58. -/
def packPowerAddressBlock : Block :=
  .seq (indexOps padSetup) (.seq (.loop (.addrLT 6 34) padBody) (pushAddressWords headerSources))

private structure PadInvariant (m : Memory K) (start j : ℕ) (s : Memory K) : Prop where
  data : s.data = m.data
  read : s.index 6 = start+j
  top : s.index 57 = start-2*j
  source : s.index 7 = 8+2*j
  length : s.index 58 = 8+3*j
  zeros : ∀ i, start-2*j ≤ i → i < start → s.index i = 0
  frame : ∀ i, i ∉ ([6,7,57,58] : List ℕ) → (i < start-2*j ∨ start ≤ i) → s.index i = m.index i

private theorem padLoop_spec (m : Memory K) (start n : ℕ) {P : K → Prop}
    (hm : m.AllData P) (h6 : m.index 6 = start) (h7 : m.index 7 = 8)
    (h8 : m.index 8 = 0) (h34 : m.index 34 = start+n)
    (h57 : m.index 57 = start) (h58 : m.index 58 = 8) (hroom : 64+2*n+8 ≤ start) :
    ∃ t, Block.Eval (Memory.AllData P) (.loop (.addrLT 6 34) padBody) m (n*12+1) t ∧
      PadInvariant m start n t := by
  apply Block.Eval.loop_invariant_exact (cost := 10) (I := PadInvariant m start)
  · exact ⟨rfl,by simpa using h6,by simpa using h57,by simpa using h7,by simpa using h58,
      by intro i h₁ h₂; simp only [Nat.mul_zero,Nat.sub_zero] at h₁;omega,fun _ _ _ => rfl⟩
  · intro j hj s h
    have hs : s.AllData P := by intro i; rw [h.data];exact hm i
    have h34' : s.index 34 = start+n := (h.frame 34 (by decide) (Or.inl (by omega))).trans h34
    have h8' : s.index 8 = 0 := (h.frame 8 (by decide) (Or.inl (by omega))).trans h8
    refine ⟨by simp [Cond.test, h.read,h34',hj],?_⟩
    obtain ⟨u,run,ud,up,uw,uf⟩ := pushAddressWords_spec [8,8] s (start-2*j) hs h.top
      (by simp;omega) (by simp)
    let t : Memory K := ⟨u.data, indicesAfter padBumps u.index⟩
    have bumps := indexOps_eval padBumps u run.safe_end
    have tf (i : ℕ) (h6' : i ≠ 6) (h7' : i ≠ 7) (h58' : i ≠ 58) :
        t.index i = u.index i := by
      apply indexOps_frame
      intro op hop
      simp only [padBumps,List.mem_cons,List.not_mem_nil,or_false] at hop
      rcases hop with rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [IndexOp.dst] <;> omega
    have ufLow (i : ℕ) (hi : i < 64) (h57' : i ≠ 57) : u.index i = s.index i :=
      uf i h57' (Or.inl (by simp;omega))
    have t6 : t.index 6 = u.index 6+1 := by
      simp [t,indicesAfter,padBumps,IndexOp.dst,IndexOp.value]
    have t7 : t.index 7 = u.index 7+2 := by
      simp [t,indicesAfter,padBumps,IndexOp.dst,IndexOp.value]
    have t58 : t.index 58 = u.index 58+3 := by
      simp [t,indicesAfter,padBumps,IndexOp.dst,IndexOp.value]
    refine ⟨t,run.seq bumps,⟨ud.trans h.data,?_,?_,?_,?_,?_,?_⟩⟩
    · rw [t6,ufLow 6 (by decide) (by decide),h.read];omega
    · rw [tf 57 (by decide) (by decide) (by decide),up];simp;omega
    · rw [t7,ufLow 7 (by decide) (by decide),h.source];omega
    · rw [t58,ufLow 58 (by decide) (by decide),h.length];omega
    · intro i hi hstart
      rw [tf i (by omega) (by omega) (by omega)]
      by_cases prev : start-2*j ≤ i
      · exact (uf i (by omega) (Or.inr prev)).trans (h.zeros i prev hstart)
      · have which : i = start-2*j-1 ∨ i = start-2*j-1-1 := by omega
        rcases which with rfl|rfl
        · simpa [h8'] using uw 0 (by decide)
        · simpa [h8'] using uw 1 (by decide)
    · intro i hi hf
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
      rw [tf i hi.1 hi.2.1 hi.2.2.2,uf i hi.2.2.1 (by simp;omega)]
      exact h.frame i (by simpa using hi) (by omega)
  · intro s h
    have h34' : s.index 34 = start+n := (h.frame 34 (by decide) (Or.inl (by omega))).trans h34
    refine ⟨by simp [Cond.test,h.read,h34'],?_⟩
    intro i
    rw [h.data]
    exact hm i

/-- Scratch index registers used by the in-place canonical address-prefix writer. -/
def powerAddressScratch : List ℕ := [6,7,8,9,10,11,12,13,57,58]

/-- The actual prefix on the native RAM is the entire canonical address input of
the signed-binary interpreter, with a linear exact cost in the raw token count. -/
theorem packPowerAddressBlock_spec (ts : List PowerToken) (m : Memory K) (start : ℕ)
    {P : K → Prop} (hm : m.AllData P) (hstart : m.index 59 = start)
    (hend : m.index 34 = start+ts.length) (hroom : 64+2*ts.length+8 ≤ start)
    (values : ∀ i, ∀ hi : i < ts.length, m.index (start+i) = ts[i].code) :
    ∃ t, Block.Eval (Memory.AllData P) packPowerAddressBlock m (12*ts.length+27) t ∧
      t.data = m.data ∧ t.index 57 = start-(2*ts.length+8) ∧
      t.index 58 = (powerEncoderAddressInput ts).length ∧
      (∀ i, ∀ hi : i < (powerEncoderAddressInput ts).length,
        t.index (start-(2*ts.length+8)+i) = (powerEncoderAddressInput ts)[i]) ∧
      ∀ i, i ∉ powerAddressScratch → (i < start-(2*ts.length+8) ∨ start ≤ i) →
        t.index i = m.index i := by
  let a : Memory K := ⟨m.data,indicesAfter padSetup m.index⟩
  have ea := indexOps_eval padSetup m hm
  have aframe (i : ℕ) (hi : i ∉ powerAddressScratch) : a.index i = m.index i := by
    apply indexOps_frame
    intro op ho
    simp only [padSetup,List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [IndexOp.dst] <;> (simp [powerAddressScratch] at hi; omega)
  have a6 : a.index 6 = start := by simp [a,indicesAfter,padSetup,IndexOp.dst,IndexOp.value,hstart]
  have a7 : a.index 7 = 8 := by simp [a,indicesAfter,padSetup,IndexOp.dst,IndexOp.value]
  have a8 : a.index 8 = 0 := by simp [a,indicesAfter,padSetup,IndexOp.dst,IndexOp.value]
  have a57 : a.index 57 = start := by simp [a,indicesAfter,padSetup,IndexOp.dst,IndexOp.value,hstart]
  have a58 : a.index 58 = 8 := by simp [a,indicesAfter,padSetup,IndexOp.dst,IndexOp.value]
  obtain ⟨b,eb,inv⟩ := padLoop_spec a start ts.length ea.safe_end a6 a7 a8
    ((aframe 34 (by decide)).trans hend) a57 a58 hroom
  obtain ⟨t,et,td,top,head,tf⟩ := pushAddressWords_spec headerSources b (start-2*ts.length)
    eb.safe_end inv.top (by simp [headerSources];omega) (by decide)
  have breg (i : ℕ) (hi : i ∈ ([8,9,10,11,12,13] : List ℕ)) :
      b.index i = a.index i := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> apply inv.frame <;> first | decide | (left;omega)
  have outside (i : ℕ) (hi : i ∉ powerAddressScratch)
      (hf : i < start-(2*ts.length+8) ∨ start ≤ i) : t.index i = m.index i := by
    have hi' : i ∉ ([6,7,57,58] : List ℕ) := by
      simp [powerAddressScratch] at hi; simp_all
    have h57' : i ≠ 57 := by simp [powerAddressScratch] at hi;tauto
    exact (tf i h57' (by simp [headerSources];omega)).trans
      ((inv.frame i hi' (by omega)).trans (aframe i hi))
  have hh (i : ℕ) (hi : i < 8) :
      t.index (start-(2*ts.length+8)+i) =
        ([2*ts.length+8,3*ts.length+8,8,0,1,2,3,4] : List ℕ)[i] := by
    have wi := head (7-i) (by simp [headerSources];omega)
    have hx : start-2*ts.length-1-(7-i)=start-(2*ts.length+8)+i := by omega
    rw [hx] at wi
    interval_cases i <;> first
      | simpa [headerSources,inv.source,inv.length,Nat.add_comm] using wi
      | simpa [headerSources,breg _ (by decide : (13:ℕ) ∈ _),a,indicesAfter,padSetup,IndexOp.dst,IndexOp.value] using wi
      | simpa [headerSources,breg _ (by decide : (8:ℕ) ∈ _),a,indicesAfter,padSetup,IndexOp.dst,IndexOp.value] using wi
      | simpa [headerSources,breg _ (by decide : (9:ℕ) ∈ _),a,indicesAfter,padSetup,IndexOp.dst,IndexOp.value] using wi
      | simpa [headerSources,breg _ (by decide : (10:ℕ) ∈ _),a,indicesAfter,padSetup,IndexOp.dst,IndexOp.value] using wi
      | simpa [headerSources,breg _ (by decide : (11:ℕ) ∈ _),a,indicesAfter,padSetup,IndexOp.dst,IndexOp.value] using wi
      | simpa [headerSources,breg _ (by decide : (12:ℕ) ∈ _),a,indicesAfter,padSetup,IndexOp.dst,IndexOp.value] using wi
  refine ⟨t,?_,td.trans inv.data,?_,?_,?_,outside⟩
  · convert ea.seq (eb.seq et) using 1 <;> first | rfl |
      (simp only [padSetup,headerSources,List.length_cons,List.length_nil];omega)
  · simpa [headerSources,Nat.sub_sub,Nat.add_comm] using top
  · rw [tf 58 (by decide) (Or.inl (by simp [headerSources];omega)),inv.length]
    simp [powerEncoderAddressInput];omega
  · intro i hi
    let hd : List ℕ := [2*ts.length+8,3*ts.length+8,8,0,1,2,3,4]
    change t.index _ = (hd ++ (List.replicate (2*ts.length) 0 ++ ts.map PowerToken.code))[i]
    by_cases hlow : i < 8
    · exact (hh i hlow).trans (List.getElem_append_left (show i < hd.length from hlow)).symm
    · refine Eq.trans ?_ (List.getElem_append_right (show hd.length ≤ i from Nat.le_of_not_gt hlow)).symm
      have htail : i-8 < (List.replicate (2*ts.length) 0 ++ ts.map PowerToken.code).length := by
        simp [powerEncoderAddressInput] at hi
        simp; omega
      change t.index _ = (List.replicate (2*ts.length) 0 ++ ts.map PowerToken.code)[i-8]'htail
      by_cases hmid : i-8 < 2*ts.length
      · refine Eq.trans ?_ (List.getElem_append_left (show i-8 < (List.replicate (2*ts.length) (0:ℕ)).length by simpa using hmid)).symm
        simp only [List.getElem_replicate]
        rw [tf _ (by omega) (Or.inr (by omega))]
        exact inv.zeros _ (by omega) (by omega)
      · refine Eq.trans ?_ (List.getElem_append_right (show (List.replicate (2*ts.length) (0:ℕ)).length ≤ i-8 by simpa using Nat.le_of_not_gt hmid)).symm
        simp only [List.length_replicate,List.getElem_map]
        have hi' : i-8-2*ts.length < ts.length := by simp [powerEncoderAddressInput] at hi;omega
        have heq : start-(2*ts.length+8)+i=start+(i-8-2*ts.length) := by omega
        rw [heq,outside _ (by simp [powerAddressScratch];omega) (Or.inr (by omega))]
        exact values _ hi'

end Compression
end LinearProgramming
end Optimization
end OAI
