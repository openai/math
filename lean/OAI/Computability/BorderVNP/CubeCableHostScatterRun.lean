import OAI.Computability.BorderVNP.CubeCableHostScatter

/-! # Executing the singleton and packet host scatters in finite native words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

private theorem ready_of_kept {f : BitFields} {z t : NatState} (ready : f.Ready z)
    (keep : Kept z.reg t.reg) : f.Ready t := by
  refine ⟨(keep 0 (by decide) (by decide)).trans ready.1,
    (keep 1 (by decide) (by decide)).trans ready.2.1,
    (keep 2 (by decide) (by decide)).trans ready.2.2.1,?_⟩
  rw [← ready.2.2.2]
  simp only [BitFields.read]
  congr 1 <;> exact keep _ (by decide) (by decide)

private theorem image_succ (f : BitFields) (before : ℕ → ℕ) (j : ℕ) :
    Function.update (f.image before j) (f.dest+j) (before (f.source j)) = f.image before (j+1) := by
  funext a
  by_cases same : a = f.dest+j
  · subst a
    simp [BitFields.image]
  · rw [Function.update_of_ne same]
    by_cases h : f.dest ≤ a ∧ a < f.dest+j
    · simp [BitFields.image,h,show f.dest ≤ a ∧ a < f.dest+(j+1) by omega]
    · simp [BitFields.image,h,show ¬(f.dest ≤ a ∧ a < f.dest+(j+1)) by omega]

private theorem step_kept (pub : Arg → ℕ) (z : NatState) :
    Kept z.reg (scatterStep.fixedEval pub z).reg := by
  intro r hr ne
  change Function.update _ 23 _ r = _
  rw [Function.update_of_ne ne]
  exact copyBit.fixedEval_protected _ _ (by decide) _ hr

set_option maxHeartbeats 1200000 in
private theorem run_step {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (f : BitFields) (fit : f.Fits w) (before : ℕ → ℕ)
    (separate : ∀ j < f.width, f.source j < f.dest ∨ f.dest+f.width ≤ f.source j)
    (j : ℕ) (hj : j < f.width) (s : Bank w) (m : Memory w)
    (ready : f.Ready (.ofWords s m)) (index : (s 23).val = j) (mem : readings m = f.image before j) :
    BoundedRun pub macros scatterStep s m scatterStep.slots (fun t =>
      Kept (readings s) t.reg ∧ t.reg 23 = j+1 ∧ t.mem = f.image before (j+1)) := by
  let z := NatState.ofWords s m
  obtain ⟨r0,r1,r2,fields⟩ := ready
  change z.reg 0 = 0 at r0
  change z.reg 1 = 1 at r1
  change z.reg 2 = 2 at r2
  change z.reg 23 = j at index
  change BitFields.read z.reg = f at fields
  have r12 := congrArg BitFields.singletonBase fields
  have r16 := congrArg BitFields.key fields
  have r17 := congrArg BitFields.start fields
  have r18 := congrArg BitFields.kind fields
  have r19 := congrArg BitFields.first fields
  have r20 := congrArg BitFields.vertex fields
  have r21 := congrArg BitFields.side fields
  have r22 := congrArg BitFields.dest fields
  have r24 := congrArg BitFields.packetBase fields
  have r25 := congrArg BitFields.blocks fields
  have r26 := congrArg BitFields.bc fields
  have r27 := congrArg BitFields.bankWidth fields
  have r28 := congrArg BitFields.selectorWidth fields
  dsimp only [BitFields.read] at r12 r16 r17 r18 r19 r20 r21 r22 r24 r25 r26 r27 r28
  have src := fit.source j hj
  have dest : f.dest+j < 2^w := by have := fit.destination; omega
  have ordinal : f.start+j < 2^w := by have := fit.ordinals; omega
  have inc : j+1 < 2^w := by
    have r15 := congrArg BitFields.width fields
    have bound := (s 15).isLt
    change (s 15).val = f.width at r15
    omega
  have safe : scatterStep.fixedSafe w (readings pub) z := by
    by_cases single : f.kind = 0
    · rw [BitFields.source,ite_eq_left single] at src
      have a : f.key*(f.blocks*f.bc) < 2^w := by omega
      have b : f.singletonBase+f.key*(f.blocks*f.bc) < 2^w := by omega
      simp (config := {decide := true}) [scatterStep,copyBit,singletonSource,Code.block,Code.fixedSafe,
        Code.fixedEval,Code.safeReadOnly,Code.evalNat,addressOp,addressOpFits,index,r0,r1,r12,r16,r17,
        r18,r22,r25,r26,single,ordinal,fit.stride single,a,b,src,dest,inc]
    · rw [BitFields.source,ite_eq_right single] at src
      have bpos := fit.divisor single (Nat.zero_lt_of_lt hj)
      have packet := fit.packet j hj single
      have port := fit.port single (Nat.zero_lt_of_lt hj)
      have a : (f.first+(f.start+j)/f.bc)*f.bankWidth < 2^w := by omega
      have b : f.packetBase+(f.first+(f.start+j)/f.bc)*f.bankWidth < 2^w := by omega
      have c : f.packetBase+(f.first+(f.start+j)/f.bc)*f.bankWidth+f.selectorWidth < 2^w := by omega
      have v : 2*f.vertex < 2^w := by omega
      have vs : (2*f.vertex+f.side)*f.bc < 2^w := by omega
      have s0 : f.packetBase+(f.first+(f.start+j)/f.bc)*f.bankWidth+f.selectorWidth+
        (2*f.vertex+f.side)*f.bc < 2^w := by omega
      simp (config := {decide := true}) [scatterStep,copyBit,packetSource,Code.block,Code.fixedSafe,
        Code.fixedEval,Code.safeReadOnly,Code.evalNat,addressOp,addressOpFits,index,r0,r1,r2,r17,r18,r19,
        r20,r21,r22,r24,r26,r27,r28,single,ordinal,bpos,packet,port,a,b,c,v,vs,s0,src,dest,inc]
  apply (scatterStep.runFixed pub macros s m safe).mono le_rfl
  rintro t rfl
  refine ⟨step_kept _ _, ?_, ?_⟩
  · change (scatterStep.fixedEval (readings pub) z).reg 23 = _
    have k23 := copyBit.fixedEval_protected (readings pub) z (lo := 30) (by decide) 23 (by decide)
    have k1 := copyBit.fixedEval_protected (readings pub) z (lo := 30) (by decide) 1 (by decide)
    simp only [scatterStep,Code.fixedEval,Code.evalNat,addressOp,Function.update_self,k23,k1,index,r1]
  · have read : z.mem (f.source j) = before (f.source j) := by
      change readings m (f.source j) = _
      rw [mem,BitFields.image,ite_eq_right (by rcases separate j hj with hs|hs <;> omega)]
    have wrote : (scatterStep.fixedEval (readings pub) z).mem =
        Function.update z.mem (f.dest+j) (z.mem (f.source j)) := by
      by_cases single : f.kind = 0
      · simp (config := {decide := true}) [BitFields.source,scatterStep,copyBit,singletonSource,Code.block,
          Code.fixedEval,Code.evalNat,addressOp,index,r0,r12,r16,r17,r18,r22,r25,r26,single]
      · simp (config := {decide := true}) [BitFields.source,scatterStep,copyBit,packetSource,Code.block,
          Code.fixedEval,Code.evalNat,addressOp,index,r0,r2,r17,r18,r19,r20,r21,r22,r24,r26,r27,r28,single]
    change (scatterStep.fixedEval (readings pub) z).mem = _
    rw [wrote,read]
    change Function.update (readings m) _ _ = _
    rw [mem,image_succ]

/-- The actual finite-word scatter visits each bit once, retains all caller
registers except its inner cursor and scratch bank, and modifies only the
cable's contiguous port interval. Both branches read the original source bit. -/
theorem run_scatterBits {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (f : BitFields) (fit : f.Fits w)
    (separate : ∀ j < f.width, f.source j < f.dest ∨ f.dest+f.width ≤ f.source j)
    (s : Bank w) (m : Memory w) (ready : f.Ready (.ofWords s m)) :
    BoundedRun pub macros scatterBits s m (2+f.width*(scatterStep.slots+1)) (fun z =>
      Kept (readings s) z.reg ∧ z.reg 23 = f.width ∧ z.mem = f.image (readings m) f.width) := by
  let P (j : ℕ) (z : NatState) := Kept (readings s) z.reg ∧ z.reg 23 = j ∧ z.mem = f.image (readings m) j
  have regs (j : ℕ) (z : NatState) (hz : P j z) : z.reg 23 = j ∧ z.reg 15 = f.width := by
    exact ⟨hz.2.1,(hz.1 15 (by decide) (by decide)).trans (congrArg BitFields.width ready.2.2.2)⟩
  have step (j : ℕ) (hj : j < f.width) (u : Bank w) (mu : Memory w) (hz : P j (.ofWords u mu)) :
      BoundedRun pub macros scatterStep u mu scatterStep.slots (P (j+1)) := by
    apply (run_step pub macros f fit (readings m) separate j hj u mu (ready_of_kept ready hz.1) hz.2.1 hz.2.2).mono le_rfl
    rintro z ⟨keep,rest⟩
    exact ⟨fun r hr ne => (keep r hr ne).trans (hz.1 r hr ne),rest⟩
  have init := (Code.copy 23 0).runFixed pub macros s m trivial
  have run := init.seq (b := .whileLt 23 15 scatterStep) (t := (f.width-0)*(scatterStep.slots+1)+1) (Q := P f.width)
    (fun u mu hu => run_counted_loop pub macros 23 15 scatterStep f.width scatterStep.slots P regs step
      0 (Nat.zero_le _) u mu (by
        rw [hu]
        refine ⟨fun r _ ne => Function.update_of_ne ne ..,ready.1,?_⟩
        funext a
        change readings m a = f.image (readings m) 0 a
        simp only [BitFields.image,Nat.add_zero,ite_eq_right (show ¬(f.dest ≤ a ∧ a < f.dest) by omega)]))
  exact run.mono (by change 1+((f.width-0)*(scatterStep.slots+1)+1) ≤ _; rw [Nat.sub_zero]; omega)
    (fun _ x => x)

end Cube.HostScatter

end BorderVNP
end Computability
end OAI
