import OAI.Computability.BorderVNP.RoutingISAAdvice
import OAI.Computability.BorderVNP.RoutingISACheckLoop

/-! # Exact memory image of the literal advice copy -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- The address directory for one bit of advice in each of the first processors. -/
structure AdviceLayout where
  /-- Offset from the start of each source processor's literal. -/
  offset : ℕ
  /-- Number of actual copied words. -/
  count : ℕ
  /-- Start of the consecutive output array. -/
  dst : ℕ

/-- The three directory entries are loaded from the original shared-memory frame. -/
def AdviceLayout.At (a : AdviceLayout) (pub : Arg → ℕ) (mem : ℕ → ℕ) : Prop :=
  frameField pub mem 26 = a.offset ∧ frameField pub mem 27 = a.count ∧ frameField pub mem 28 = a.dst

/-- Address of the advice bit in the literal field of the specified processor. -/
def AdviceLayout.src (a : AdviceLayout) (f : BroadcastFrame) (i : ℕ) := i*f.stride+a.offset

/-- The physical source and destination intervals are addressable and disjoint. -/
structure AdviceLayout.Fits (a : AdviceLayout) (f : BroadcastFrame) (w base : ℕ) : Prop where
  /-- The source offset belongs to the first literal, before the exterior bits. -/
  literal : a.offset < f.literal
  /-- There is an initialized processor segment for every requested advice bit. -/
  count : a.count ≤ f.processors
  /-- Every destination word fits. -/
  dest : a.dst + a.count ≤ 2^w
  /-- Stores cannot overwrite any part of an initialized processor tape. -/
  sourceDisjoint : ∀ x < f.processors*f.stride, ¬ (a.dst ≤ x ∧ x-a.dst < a.count)
  /-- Stores cannot overwrite any of the 31 boot-frame fields. -/
  frameDisjoint : ∀ j < 31, ¬ (a.dst ≤ base+j ∧ base+j-a.dst < a.count)

/-- The array after processing the first `n` source processors. -/
def AdviceLayout.copied (a : AdviceLayout) (f : BroadcastFrame) (original : ℕ → ℕ) (n x : ℕ) : ℕ :=
  if a.dst ≤ x ∧ x-a.dst < n then original (a.src f (x-a.dst)) else original x

/-- Every addressed output word is exactly the processor's original literal word. -/
theorem AdviceLayout.copied_at (a : AdviceLayout) (f : BroadcastFrame) (original : ℕ → ℕ) {i n : ℕ}
    (hi : i < n) : a.copied f original n (a.dst+i) = original (a.src f i) := by simp [copied,hi]

/-- Any physical address outside the output interval retains its original word. -/
theorem AdviceLayout.copied_outside (a : AdviceLayout) (f : BroadcastFrame) (original : ℕ → ℕ)
    {x n : ℕ} (hx : ¬ (a.dst ≤ x ∧ x-a.dst < n)) : a.copied f original n x = original x := by
  simp [copied,hx]

private theorem copied_next (a : AdviceLayout) (f : BroadcastFrame) (original : ℕ → ℕ) (i : ℕ) :
    Function.update (a.copied f original i) (a.dst+i) (original (a.src f i)) = a.copied f original (i+1) := by
  funext x
  by_cases hx : x = a.dst+i
  · subst x; simp [AdviceLayout.copied]
  · rw [Function.update_of_ne hx]
    unfold AdviceLayout.copied
    split_ifs <;> first | rfl | omega

/-- A requested literal slot is inside the corresponding processor's input segment. -/
theorem AdviceLayout.src_lt_input {a : AdviceLayout} {f : BroadcastFrame} {w base : ℕ}
    (fit : a.Fits f w base) {i : ℕ} (hi : i < a.count) : a.src f i < f.processors*f.stride := by
  have h₁ : a.offset < f.stride := by unfold BroadcastFrame.stride; have := fit.literal; omega
  have h₂ := Nat.mul_le_mul_right f.stride (hi.trans_le fit.count : i < f.processors)
  rw [Nat.succ_mul] at h₂
  unfold src; omega

private structure AdviceState (a : AdviceLayout) (f : BroadcastFrame) (original : ℕ → ℕ) (bank : Reg → ℕ)
    (i : ℕ) (z : NatState) : Prop where
  off : z.reg 34 = a.offset
  count : z.reg 35 = a.count
  dst : z.reg 36 = a.dst
  stride : z.reg 38 = f.stride
  cursor : z.reg 39 = i
  one : z.reg 40 = 1
  two : z.reg 41 = 2
  memory : z.mem = a.copied f original i
  keep : ∀ j : Reg, j.val < 30 → z.reg j = bank j

private theorem advice_setup {w : ℕ} (f : BroadcastFrame) (a : AdviceLayout) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (image : f.At (readings pub) (readings m)) (fields : a.At (readings pub) (readings m))
    (fit : f.Fits w (pub 0).val) (room : a.Fits f w (pub 0).val) :
    BoundedRun pub macros literalAdviceSetup s m literalAdviceSetup.slots
      (AdviceState a f (readings m) (readings s) 0) := by
  obtain ⟨_,r,p,lit,link,_,_⟩ := image
  obtain ⟨off,count,dst⟩ := fields
  have hs : f.stride < 2^w := by
    have hh := Nat.le_mul_of_pos_left f.stride fit.procs
    exact hh.trans_lt (fit.input.trans_lt (pub 0).isLt)
  have size : (pub 0).val + 28 < 2^w := by have := fit.frame; have := fit.out; omega
  have nonzero : w ≠ 0 := by rintro rfl; simp at size
  have read (d : Reg) (k : Word 8) (hk : k.val ≤ 28) (t : Reg → ℕ) :
      (readFrame d 62 63 k).safeReadOnly w (readings pub) (readings m) t := by
    simp (config := {decide := true}) [readFrame,Code.block,Code.safeReadOnly,Code.evalNat,addressOpFits,readings]
    omega
  have guard : ¬ f.processors < a.count := Nat.not_lt.mpr room.count
  have safe : literalAdviceSetup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [literalAdviceSetup,Code.block,readFrameFixed,requireLt,
      Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,r,p,lit,link,off,count,dst,guard,
      room.literal,read _ _ (by decide : (1:Word 8).val ≤ 28),
      read _ _ (by decide : (2:Word 8).val ≤ 28), read _ _ (by decide : (3:Word 8).val ≤ 28),
      read _ _ (by decide : (4:Word 8).val ≤ 28), read _ _ (by decide : (26:Word 8).val ≤ 28),
      read _ _ (by decide : (27:Word 8).val ≤ 28), read _ _ (by decide : (28:Word 8).val ≤ 28)]
    have := fit.three
    unfold BroadcastFrame.stride at hs
    omega
  obtain ⟨es,t,run,cap,val⟩ := literalAdviceSetup.runReadOnly pub macros m s safe
  refine ⟨es,t,m,run,cap,?_⟩
  constructor
  case keep =>
    intro j hj
    exact (congrFun val j).trans (literalAdviceSetup.evalNat_protected _ _ _
      (by decide : literalAdviceSetup.protects 30 = true) j hj)
  case memory => funext x; simp [AdviceLayout.copied,NatState.ofWords]
  all_goals
    change readings t _ = _
    rw [val]
    simp (config := {decide := true}) [literalAdviceSetup,Code.block,
      Code.evalNat,readFrameFixed,addressOp,requireLt,r,p,lit,link,off,count,dst,guard,
      room.literal,BroadcastFrame.stride,Nat.add_comm,Nat.mul_comm]

private theorem advice_bit {w : ℕ} (f : BroadcastFrame) (a : AdviceLayout) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (original : ℕ → ℕ) (bank : Reg → ℕ)
    (fit : f.Fits w (pub 0).val) (room : a.Fits f w (pub 0).val)
    (boolean : ∀ i < a.count, original (a.src f i) < 2)
    (i : ℕ) (hi : i < a.count) (s : Bank w) (m : Memory w)
    (hs : AdviceState a f original bank i (.ofWords s m)) :
    BoundedRun pub macros literalAdviceBit s m literalAdviceBit.slots (AdviceState a f original bank (i+1)) := by
  let st := NatState.ofWords s m
  have off : st.reg 34 = a.offset := hs.off
  have count : st.reg 35 = a.count := hs.count
  have dest : st.reg 36 = a.dst := hs.dst
  have stride : st.reg 38 = f.stride := hs.stride
  have cur : st.reg 39 = i := hs.cursor
  have one : st.reg 40 = 1 := hs.one
  have two : st.reg 41 = 2 := hs.two
  have addr := AdviceLayout.src_lt_input room hi
  have inside : i*f.stride+a.offset < 2^w := addr.trans_le (fit.input.trans (pub 0).isLt.le)
  have outside : ¬ (a.dst ≤ a.src f i ∧ a.src f i - a.dst < i) :=
    fun h => room.sourceDisjoint _ addr ⟨h.1,h.2.trans hi⟩
  have originalBit : st.mem (i*f.stride+a.offset) = original (a.src f i) :=
    (congrFun hs.memory _).trans (a.copied_outside f original outside)
  have bit := boolean i hi
  have stridePos : 0 < f.stride := by unfold BroadcastFrame.stride; have := room.literal; omega
  have procFits : f.processors < 2^w :=
    (Nat.le_mul_of_pos_right _ stridePos).trans_lt (fit.input.trans_lt (pub 0).isLt)
  have safe : literalAdviceBit.fixedSafe w (readings pub) st := by
    simp (config := {decide := true}) [literalAdviceBit,Code.block,Code.fixedSafe,Code.fixedEval,
      requireLt,Code.evalNat,Code.safeReadOnly,addressOpFits,addressOp,cur,stride,off,dest,one,two,originalBit,bit]
    have := room.dest
    have := room.count
    omega
  apply (literalAdviceBit.runFixed pub macros s m safe).mono le_rfl
  intro z hz
  rw [hz]
  constructor
  case keep =>
    intro j hj
    exact (literalAdviceBit.fixedEval_protected (readings pub) st
      (by decide : literalAdviceBit.protects 30 = true) j hj).trans (hs.keep j hj)
  case memory =>
    change (literalAdviceBit.fixedEval (readings pub) st).mem = _
    simp (config := {decide := true}) [literalAdviceBit,Code.block,Code.fixedEval,Code.evalNat,
      requireLt,addressOp,cur,stride,off,dest,two,originalBit,bit,← copied_next]
    exact congrArg (fun b => Function.update b (a.dst+i) (original (a.src f i))) hs.memory
  all_goals
    change (literalAdviceBit.fixedEval (readings pub) st).reg _ = _
    simp (config := {decide := true}) [literalAdviceBit,Code.block,Code.fixedEval,Code.evalNat,
      requireLt,addressOp,cur,one,off,dest,two,stride,originalBit,bit,count]

/-- A fitted finite word table copies exactly the declared physical literal bits.
The formula for the memory image covers every address, including untouched
input tapes and frame slots. Each copied bit uses a constant number of ticks. -/
theorem readLiteralAdvice_run {w : ℕ} (f : BroadcastFrame) (a : AdviceLayout) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (image : f.At (readings pub) (readings m)) (fields : a.At (readings pub) (readings m))
    (fit : f.Fits w (pub 0).val) (room : a.Fits f w (pub 0).val)
    (boolean : ∀ i < a.count, readings m (a.src f i) < 2) :
    BoundedRun pub macros readLiteralAdvice s m (literalAdviceSetup.slots+a.count*(literalAdviceBit.slots+1)+1)
      (fun z => z.mem = a.copied f (readings m) a.count ∧ ∀ j : Reg, j.val < 30 → z.reg j = (s j).val) := by
  have start := advice_setup f a pub macros s m image fields fit room
  let I := AdviceState a f (readings m) (readings s)
  have loop t mt (h : I 0 (.ofWords t mt)) := run_counted_loop pub macros 39 35 literalAdviceBit
    a.count literalAdviceBit.slots I (fun _ _ h => ⟨h.cursor,h.count⟩)
    (fun i hi => advice_bit f a pub macros (readings m) (readings s) fit room boolean i hi)
    0 (Nat.zero_le _) t mt h
  apply (start.seq loop).mono
  · simp [Nat.add_assoc]
  · exact fun _ h => ⟨h.memory,h.keep⟩

/-- Arbitrary successful native returns have the identical memory image and
preserve the same low registers. -/
theorem readLiteralAdvice_test {w : ℕ} (f : BroadcastFrame) (a : AdviceLayout) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (image : f.At (readings pub) (readings m)) (fields : a.At (readings pub) (readings m))
    (fit : f.Fits w (pub 0).val) (room : a.Fits f w (pub 0).val)
    (boolean : ∀ i < a.count, readings m (a.src f i) < 2) :
    TestRun pub macros readLiteralAdvice s m (literalAdviceSetup.slots+a.count*(literalAdviceBit.slots+1)+1)
      True (fun z => z.mem = a.copied f (readings m) a.count ∧ ∀ j : Reg, j.val < 30 → z.reg j = (s j).val) :=
  (readLiteralAdvice_run f a pub macros s m image fields fit room boolean).asTest (by decide)

end RoutingISA

end BorderVNP
end Computability
end OAI
