import OAI.Computability.BorderVNP.CubeCableHostScatterRun
import OAI.Computability.BorderVNP.RoutingISACheckLoop
import OAI.Computability.BorderVNP.RoutingISAPaddingScan

/-! # Physical verification of a directed bin's unused bits

The verifier uses the identical singleton and packet addressing instructions as
the actual host scatter. It checks both physical endpoint banks without writing
the memory and consumes time proportional to the inspected padding interval.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM HostScatter
open private requireEq_return from OAI.Computability.BorderVNP.RoutingISAPaddingScan
open private ready_of_kept from OAI.Computability.BorderVNP.CubeCableHostScatterRun

/-- Compute and load the bit at the within-bin ordinal start+cursor. -/
def readBit : Code := .block [.binary .add 30 17 23,.ifEq 18 0 singletonSource packetSource,.load 32 31]

/-- Reject exactly a nonzero loaded bit, and advance to the next slot on success. -/
def bitStep : Code := .seq readBit (.seq (requireEq 32 0) (.binary .add 23 23 1))

/-- Visit the entire cached interval of the actual physical singleton or packet bank. -/
def bits : Code := .seq (.copy 23 0) (.whileLt 23 15 bitStep)

private theorem checkedEq {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (x y : Reg) :
    TestRun pub macros (requireEq x y) s m (requireEq x y).slots (s x = s y) (· = NatState.ofWords s m) := by
  have run (eq : s x = s y) : BoundedRun pub macros (requireEq x y) s m (requireEq x y).slots (· = NatState.ofWords s m) := by
    have safe : (requireEq x y).fixedSafe w (readings pub) (.ofWords s m) := by
      simp [requireEq,Code.fixedSafe,NatState.ofWords,readings,eq,Code.safeReadOnly]
    refine ((requireEq x y).runFixed pub macros s m safe).mono le_rfl ?_
    intro z h
    simpa [requireEq,Code.fixedEval,Code.evalNat,NatState.ofWords,readings,eq] using h
  refine ⟨run,?_⟩
  intro es t mt h
  have eq := requireEq_return h
  exact ⟨eq,((run eq).asTest (by rfl)).sound h |>.2⟩

set_option maxHeartbeats 1200000 in
/-- The arithmetic in both genuine source-address branches fits the physical words
and loads the actual memory bit. Every cache register survives. -/
theorem run_readBit {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (f : BitFields) (fit : f.Fits w) (j : ℕ) (hj : j < f.width) (s : Bank w) (m : Memory w)
    (ready : f.Ready (.ofWords s m)) (index : (s 23).val = j) :
    BoundedRun pub macros readBit s m readBit.slots (fun z =>
      (∀ r : Reg, r.val < 30 → z.reg r = (s r).val) ∧ z.mem = readings m ∧ z.reg 32 = readings m (f.source j)) := by
  let z := NatState.ofWords s m
  change z.reg 23 = j at index
  obtain ⟨r0,r1,r2,fields⟩ := ready
  change z.reg 0 = 0 at r0
  change z.reg 2 = 2 at r2
  obtain ⟨r15,r16,r17,r18,r19,r20,r21,r22,r12,r24,r25,r26,r27,r28⟩ :=
    BitFields.mk.inj (show BitFields.read z.reg = f from fields)
  have src := fit.source j hj
  have ordinal : f.start+j < 2^w := by have := fit.ordinals; omega
  have safe : readBit.fixedSafe w (readings pub) z := by
    by_cases single : f.kind = 0
    · rw [BitFields.source,ite_eq_left single] at src
      have a : f.key*(f.blocks*f.bc) < 2^w := by omega
      have b : f.singletonBase+f.key*(f.blocks*f.bc) < 2^w := by omega
      simp (config := {decide := true}) [readBit,singletonSource,Code.block,Code.fixedSafe,Code.fixedEval,
        Code.safeReadOnly,Code.evalNat,addressOp,addressOpFits,index,r0,r12,r16,r17,r18,r25,r26,single,
        ordinal,fit.stride single,a,b,src]
    · rw [BitFields.source,ite_eq_right single] at src
      have bpos := fit.divisor single (Nat.zero_lt_of_lt hj)
      have packet := fit.packet j hj single
      have port := fit.port single (Nat.zero_lt_of_lt hj)
      have a : (f.first+(f.start+j)/f.bc)*f.bankWidth < 2^w := by omega
      have b : f.packetBase+(f.first+(f.start+j)/f.bc)*f.bankWidth < 2^w := by omega
      have c : f.packetBase+(f.first+(f.start+j)/f.bc)*f.bankWidth+f.selectorWidth < 2^w := by omega
      have v : 2*f.vertex < 2^w := by omega
      have vs : (2*f.vertex+f.side)*f.bc < 2^w := by omega
      have s0 : f.packetBase+(f.first+(f.start+j)/f.bc)*f.bankWidth+f.selectorWidth+(2*f.vertex+f.side)*f.bc < 2^w := by omega
      simp (config := {decide := true}) [readBit,packetSource,Code.block,Code.fixedSafe,Code.fixedEval,
        Code.safeReadOnly,Code.evalNat,addressOp,addressOpFits,index,r0,r2,r17,r18,r19,r20,r21,r24,r26,r27,r28,
        single,ordinal,bpos,packet,port,a,b,c,v,vs,s0,src]
  refine (readBit.runFixed pub macros s m safe).mono le_rfl ?_
  rintro _ rfl
  refine ⟨fun r hr => readBit.fixedEval_protected (readings pub) z (by decide) r hr,?_⟩
  change (readBit.fixedEval (readings pub) z).mem = z.mem ∧
    (readBit.fixedEval (readings pub) z).reg 32 = z.mem (f.source j)
  by_cases single : f.kind = 0
  · simp (config := {decide := true}) [readBit,BitFields.source,singletonSource,Code.block,Code.fixedEval,Code.evalNat,
      addressOp,index,r0,r12,r16,r17,r18,r25,r26,single]
  · simp (config := {decide := true}) [readBit,BitFields.source,packetSource,Code.block,Code.fixedEval,Code.evalNat,
      addressOp,index,r0,r2,r17,r18,r19,r20,r21,r24,r26,r27,r28,single]

/-- Cost charged for one physical bit and its loop guard. -/
def bitCost := readBit.slots+(requireEq 32 0).slots+2

/-- The native padding scan is an exact test, including the empty interval. It
preserves the complete memory and the public cache and outer pair cursor. -/
theorem run_bits {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (f : BitFields) (fit : f.Fits w) (s : Bank w) (m : Memory w) (ready : f.Ready (.ofWords s m)) :
    TestRun pub macros bits s m (2+f.width*bitCost) (∀ j < f.width, readings m (f.source j)=0)
      (fun z => Kept (readings s) z.reg ∧ z.mem=readings m) := by
  let I (j : ℕ) (z : NatState) := Kept (readings s) z.reg ∧ z.reg 23=j ∧ z.mem=readings m
  have regs (j : ℕ) (z : NatState) (hz : I j z) : z.reg 23=j ∧ z.reg 15=f.width := by
    exact ⟨hz.2.1,congrArg BitFields.width (ready_of_kept ready hz.1).2.2.2⟩
  have step (j : ℕ) (hj : j<f.width) (t : Bank w) (mt : Memory w) (h : I j (.ofWords t mt)) :
      TestRun pub macros bitStep t mt (readBit.slots+((requireEq 32 0).slots+1))
        (readings m (f.source j)=0) (I (j+1)) := by
    have rd := (run_readBit pub macros f fit j hj t mt (ready_of_kept ready h.1) h.2.1).asTest (by decide)
    refine (rd.seq (b := .seq (requireEq 32 0) (.binary .add 23 23 1))
      (ob := readings m (f.source j)=0 ∧ True) (cb := (requireEq 32 0).slots+1) ?_).mono le_rfl (by simp) (fun _ => id)
    intro t₁ m₁ rdout
    obtain ⟨kept,mem,bit⟩ := rdout
    have same (i : Reg) (hi : i.val<30) (hne : i ≠ 23) : (t₁ i).val=(s i).val := (kept i hi).trans (h.1 i hi hne)
    have zr : (t₁ 0).val = 0 := (same 0 (by decide) (by decide)).trans ready.1
    have one : (t₁ 1).val = 1 := (same 1 (by decide) (by decide)).trans ready.2.1
    have cur : (t₁ 23).val=j := (kept _ (by decide)).trans h.2.1
    have tested : t₁ 32=t₁ 0 ↔ readings m (f.source j)=0 := by
      rw [Fin.ext_iff]
      rw [show (t₁ 32).val = readings m (f.source j) from bit.trans (congrFun h.2.2 _),zr]
    have check := (checkedEq pub macros t₁ m₁ 32 0).mono le_rfl tested (fun _ => id)
    apply check.seq
    intro t₂ m₂ eq
    have same₂ := congrArg NatState.reg eq
    have mem₂ := congrArg NatState.mem eq
    have inc : j+1 < 2^w := by
      have cap := (s 15).isLt
      have wd : (s 15).val = f.width := congrArg BitFields.width ready.2.2.2
      omega
    have ix : (t₂ 23).val=j := (congrFun same₂ 23).trans cur
    have un : (t₂ 1).val=1 := (congrFun same₂ 1).trans one
    have safe : (Code.binary .add 23 23 1).fixedSafe w (readings pub) (.ofWords t₂ m₂) := by
      simpa [Code.fixedSafe,Code.safeReadOnly,NatState.ofWords,readings,addressOpFits,ix,un] using inc
    apply ((Code.binary .add 23 23 1).runFixed pub macros t₂ m₂ safe).asTest (by decide) |>.mono le_rfl Iff.rfl
    rintro z rfl
    refine ⟨?_,?_,mem₂.trans (mem.trans h.2.2)⟩
    · intro i hi hne
      change Function.update _ 23 _ i = _
      rw [Function.update_of_ne hne]
      exact (congrFun same₂ i).trans (same i hi hne)
    · simp only [Code.fixedEval,Code.evalNat,addressOp,Function.update_self,NatState.ofWords,readings,ix,un]
  have init := ((Code.copy 23 0).runFixed pub macros s m trivial).asTest (by decide)
  refine (init.seq (b := .whileLt 23 15 bitStep) (cb := (∑ _j ∈ Finset.Ico 0 f.width, bitCost)+1)
    (ob := ∀ j, 0 ≤ j → j < f.width → readings m (f.source j)=0) (Q := I f.width) ?_).mono ?_ (by simp) ?_
  · intro t mt eq
    apply (test_counted_loop 23 15 bitStep f.width (fun _ => readBit.slots+((requireEq 32 0).slots+1))
      (fun j => readings m (f.source j)=0) I regs step 0 (Nat.zero_le _) t mt ?_).mono ?_ Iff.rfl (fun _ => id)
    · rw [eq]; exact ⟨fun r _ h => Function.update_of_ne h ..,ready.1,rfl⟩
    · unfold bitCost
      rw [show readBit.slots+((requireEq 32 0).slots+1)+1 = readBit.slots+(requireEq 32 0).slots+2 by omega]
  · simp [Code.slots,Nat.add_comm]; omega
  · intro z hz; exact ⟨hz.1,hz.2.2⟩

end Cube.Padding

end BorderVNP
end Computability
end OAI
