import OAI.Computability.BorderVNP.RoutingISAAdviceProof
import OAI.Computability.BorderVNP.DiagonalTallyBitsPack
import Mathlib.Algebra.Order.Floor.Div

/-! # Distributed geometry advice in the processors' actual literal fields

Bits of the geometry circuit are stored consecutively in a fixed stripe of each
processor literal. The finite RAM table reads only the occupied prefix of these
stripes. Its destination is a dense sequence of bit words for the shared gate reader.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryAdvice

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Runtime locations and public sizes of the striped advice. -/
structure Stripe where
  /-- Offset of the geometry bits within each processor's literal. -/
  offset : ℕ
  /-- Bits reserved per processor. -/
  width : ℕ
  /-- First dense scratch address. -/
  dense : ℕ
  /-- Total number of native words in the encoded advice. -/
  words : ℕ

/-- Public scalar arguments are actual shared-memory words in the extended frame. -/
def Stripe.At (a : Stripe) (w : ℕ) (pub : Arg → ℕ) (mem : ℕ → ℕ) : Prop :=
  frameField pub mem 96 = a.offset ∧ frameField pub mem 97 = a.width ∧
    frameField pub mem 98 = a.dense ∧ frameField pub mem 100 = a.words ∧ frameField pub mem 101 = w

/-- Source word for the `i`-th bit of the serialized geometry advice. -/
def Stripe.src (a : Stripe) (stride i : ℕ) := i/a.width*stride+a.offset+i%a.width

/-- Source and destination fit the real physical processor fields and memory word. -/
structure Stripe.Fits (a : Stripe) (f : BroadcastFrame) (w frame : ℕ) : Prop where
  /-- Nonempty stripe for Euclidean division. -/
  positive : 0 < a.width
  /-- The literal prefix of each processor contains its assigned stripe. -/
  literal : a.offset+a.width ≤ f.literal
  /-- Only initialized source bits are read. -/
  capacity : a.words*w ≤ f.processors*a.width
  /-- Dense storage is disjoint from physical input and the extended frame. -/
  afterFrame : frame+112 ≤ a.dense
  /-- The dense end sentinel fits the machine word. -/
  denseFit : a.dense+a.words*w < 2^w

/-- Every requested bit is in the literal of the indicated processor. -/
theorem Stripe.src_lt {a : Stripe} {f : BroadcastFrame} {w b i : ℕ} (h : a.Fits f w b)
    (hi : i < a.words*w) : a.src f.stride i < f.processors*f.stride := by
  have hp := (Nat.div_lt_iff_lt_mul h.positive).mpr (hi.trans_le h.capacity)
  have hh := Nat.mul_le_mul_right f.stride (show i/a.width+1 ≤ f.processors from hp)
  have hj := Nat.mod_lt i h.positive
  have hl := h.literal
  have hstride : f.literal ≤ f.stride := by unfold BroadcastFrame.stride; omega
  rw [Nat.succ_mul] at hh
  unfold src; omega

/-- Read geometry locations and form the processor stride and occupied bit count. -/
def beginStripe : Code := .block [
  .constant 0 0,.constant 1 1,.constant 17 2,
  readFrame 2 62 63 1,readFrame 3 62 63 2,readFrame 4 62 63 3,readFrame 5 62 63 4,
  readFrame 6 62 63 96,readFrame 7 62 63 97,readFrame 8 62 63 98,
  readFrame 9 62 63 100,readFrame 10 62 63 101,
  .binary .sub 11 2 1,.binary .mul 11 11 5,.binary .mul 16 4 17,.binary .add 11 16 11,
  .binary .mul 12 9 10,.copy 13 0]

/-- Decode the source processor and bit offset, copy the actual word, and advance. -/
def copyStripeBit : Code := .block [
  .binary .div 14 13 7,.binary .mul 14 14 11,.binary .add 14 14 6,
  .binary .mod 15 13 7,.binary .add 14 14 15,.load 16 14,
  .binary .add 15 8 13,.store 15 16,.binary .add 13 13 1]

/-- Fixed table, independent of the graph, its profiles and its Boolean circuit. -/
def readStripe : Code := .seq beginStripe (.whileLt 13 12 copyStripeBit)

/-- Memory after the first `n` geometry-advice bits have been copied. -/
def Stripe.image (a : Stripe) (stride : ℕ) {α : Type*} (m : ℕ → α) (n j : ℕ) : α :=
  if a.dense ≤ j ∧ j-a.dense < n then m (a.src stride (j-a.dense)) else m j

/-- Read the deinterleaved bit from its dense position. -/
theorem Stripe.image_at {a : Stripe} {stride n i : ℕ} {α : Type*} (m : ℕ → α) (hi : i<n) :
    a.image stride m n (a.dense+i) = m (a.src stride i) := by simp [image,hi]

/-- Other words survive the entire advice-copy prefix. -/
theorem Stripe.image_outside {a : Stripe} {stride n j : ℕ} {α : Type*} (m : ℕ → α)
    (h : j < a.dense ∨ a.dense+n ≤ j) : a.image stride m n j = m j := by
  simp [image, show ¬ (a.dense ≤ j ∧ j-a.dense<n) by omega]

private theorem image_succ (a : Stripe) (stride n : ℕ) {α : Type*} (m : ℕ → α) :
    Function.update (a.image stride m n) (a.dense+n) (m (a.src stride n)) = a.image stride m (n+1) := by
  funext j
  by_cases he : j = a.dense+n
  · subst j
    simp [Stripe.image]
  · rw [Function.update_of_ne he]
    unfold Stripe.image
    split_ifs <;> first | rfl | omega

private structure State (a : Stripe) (stride w : ℕ) (m : ℕ → ℕ) (i : ℕ) (z : NatState) : Prop where
  one : z.reg 1 = 1
  offset : z.reg 6 = a.offset
  width : z.reg 7 = a.width
  dest : z.reg 8 = a.dense
  strideEq : z.reg 11 = stride
  count : z.reg 12 = a.words*w
  cursor : z.reg 13 = i
  mem : z.mem = a.image stride m i

private theorem read_fit {w : ℕ} (d : Reg) (field : Word 8) (pub : Arg → ℕ) (mem : ℕ → ℕ)
    (s : Reg → ℕ) : (readFrame d 62 63 field).safeReadOnly w pub mem s ↔ pub 0 + field.val < 2^w := by
  simp (config := { decide := true }) [readFrame,Code.block,Code.safeReadOnly,Code.evalNat,addressOpFits]
  omega

private theorem setup_run {w : ℕ} (a : Stripe) (f : BroadcastFrame) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) (frame : f.At (readings pub) (readings m))
    (given : a.At w (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (space : a.Fits f w (pub 0).val) :
    BoundedRun pub mac beginStripe s m beginStripe.slots (State a f.stride w (readings m) 0) := by
  obtain ⟨_,R,r,lit,link,_,_⟩ := frame
  obtain ⟨o,b,d,c,v⟩ := given
  have frameRoom : readings pub 0+101 < 2^w := by change (pub 0).val+101 < _; have := space.afterFrame; have := space.denseFit; omega
  have sr : 2*f.literal+(f.teams-1)*f.link < 2^w :=
    (Nat.le_mul_of_pos_left f.stride fit.procs).trans_lt (fit.input.trans_lt (pub 0).isLt)
  have hw : w ≠ 0 := by rintro rfl; simp at frameRoom
  have safe : beginStripe.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := { decide := true }) [beginStripe,Code.block,Code.safeReadOnly,Code.evalNat,
      read_fit,readFrameFixed,addressOpFits,addressOp,R,lit,link,c,v,hw]
    have := fit.three
    have := space.denseFit
    omega
  obtain ⟨es,z,run,ct,hz⟩ := beginStripe.runReadOnly pub mac m s safe
  refine ⟨es,z,m,run,ct,?_⟩
  constructor
  case mem => funext i; simp [Stripe.image,NatState.ofWords]
  all_goals
    change readings z _ = _
    rw [hz]
    simp (config := {decide := true}) [beginStripe,Code.block,Code.evalNat,readFrameFixed,addressOp,
      BroadcastFrame.stride,R,lit,link,o,b,d,c,v,Nat.mul_comm]

private theorem copy_run {w : ℕ} (a : Stripe) (f : BroadcastFrame) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (original : ℕ → ℕ) (fit : f.Fits w (pub 0).val)
    (space : a.Fits f w (pub 0).val) (i : ℕ) (hi : i<a.words*w) (s : Bank w) (m : Memory w)
    (h : State a f.stride w original i (.ofWords s m)) :
    BoundedRun pub mac copyStripeBit s m copyStripeBit.slots (State a f.stride w original (i+1)) := by
  let z := NatState.ofWords s m
  change State a f.stride w original i z at h
  obtain ⟨hone,hoff,hb,hd,hs,hn,hi',hm⟩ := h
  have before := (a.src_lt space hi).trans_le fit.input
  have atSource : z.mem (a.src f.stride i) = original (a.src f.stride i) :=
    (congrFun hm _).trans (a.image_outside original (Or.inl (by have := space.afterFrame; omega)))
  have srcRoom := lt_trans before (pub 0).isLt
  have destRoom := space.denseFit
  have safe : copyStripeBit.fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [copyStripeBit,Code.block,Code.fixedSafe,Code.fixedEval,
      Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,hi',hs,hoff,hb,hd,hone,space.positive]
    dsimp only [Stripe.src] at srcRoom
    omega
  apply (copyStripeBit.runFixed pub mac s m safe).mono le_rfl
  intro z' hz
  rw [hz]
  change State a f.stride w original (i+1) (copyStripeBit.fixedEval (readings pub) z)
  constructor
  case mem =>
    simp (config := {decide := true}) [copyStripeBit,Code.block,Code.fixedEval,Code.evalNat,addressOp,
      hi',hs,hoff,hb,hd]
    change Function.update z.mem (a.dense+i) (z.mem (a.src f.stride i)) = _
    rw [atSource,hm,image_succ]
  all_goals
    simp (config := {decide := true}) [copyStripeBit,Code.block,Code.fixedEval,Code.evalNat,addressOp,
      hi',hs,hoff,hb,hd,hone,hn]

/-- A caller with a different startup frame can reuse the same native stripe loop.
The seven registers give unit, offset, stripe width, dense base, processor stride,
bit count and the initial zero index. -/
theorem copyStripeLoop_runs {w : ℕ} (a : Stripe) (f : BroadcastFrame) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) (fit : f.Fits w (pub 0).val)
    (space : a.Fits f w (pub 0).val) (one : (s 1).val = 1) (off : (s 6).val = a.offset)
    (width : (s 7).val = a.width) (dst : (s 8).val = a.dense) (stride : (s 11).val = f.stride)
    (count : (s 12).val = a.words*w) (zero : (s 13).val = 0) :
    ∃ es z, Runs pub mac (.whileLt 13 12 copyStripeBit) s m es z (a.image f.stride m (a.words*w)) ∧
      traceCost es ≤ (a.words*w)*(copyStripeBit.slots+1)+1 := by
  let I := State a f.stride w (readings m)
  have init : I 0 (.ofWords s m) := ⟨one,off,width,dst,stride,count,zero,by
    funext i; simp [Stripe.image,NatState.ofWords]⟩
  obtain ⟨es,z,mz,run,ct,h⟩ := run_counted_loop pub mac 13 12 copyStripeBit (a.words*w) copyStripeBit.slots I
    (fun _ _ h => ⟨h.cursor,h.count⟩) (fun i hi => copy_run a f pub mac _ fit space i hi) 0 (Nat.zero_le _) s m init
  have out : mz = a.image f.stride m (a.words*w) := by
    funext i
    apply Fin.ext
    simpa only [NatState.ofWords,readings,Stripe.image,apply_ite Fin.val] using congrFun h.mem i
  exact ⟨es,z,out ▸ run,by simpa only [Nat.sub_zero] using ct⟩

/-- Actual word loads deinterleave the complete serialized advice with nine ordinary
instructions and one loop guard per bit. The postcondition gives every memory word. -/
theorem readStripe_runs {w : ℕ} (a : Stripe) (f : BroadcastFrame) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) (frame : f.At (readings pub) (readings m))
    (given : a.At w (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (space : a.Fits f w (pub 0).val) :
    ∃ es t, Runs pub mac readStripe s m es t (a.image f.stride m (a.words*w)) ∧
      traceCost es ≤ beginStripe.slots+(a.words*w)*(copyStripeBit.slots+1)+1 := by
  obtain ⟨es,t,mt,setup,ct,h⟩ := setup_run a f pub mac s m frame given fit space
  have same : mt = m := by
    funext j
    apply Fin.ext
    simpa only [NatState.ofWords,readings,Stripe.image,Nat.not_lt_zero,and_false,ite_false] using congrFun h.mem j
  subst mt
  obtain ⟨fs,z,loop,ft⟩ := copyStripeLoop_runs a f pub mac t m fit space h.one h.offset h.width h.dest
    h.strideEq h.count h.cursor
  refine ⟨_,z,setup.seq loop,?_⟩
  rw [show traceCost (es++fs) = traceCost es+traceCost fs from VPVNP.RAMBuckets.cost_append ..]
  omega

end GeometryAdvice

end BorderVNP
end Computability
end OAI
