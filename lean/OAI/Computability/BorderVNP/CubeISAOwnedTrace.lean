import OAI.Computability.BorderVNP.CubeISAOwnedScan
import OAI.Computability.BorderVNP.DiagonalResidueRAMFrame
import OAI.Computability.BorderVNP.RoutingISATableEvents

/-! # Bounded positive executions with the exact chronological private bits

A row's physical scatter contributes private choices only in its accepted
callbacks. Counting loops and address calculation contribute ordinary ticks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Owned

open VPVNP.BurstRAM DiagonalResidueRAM Finset

/-- Bounded native return with the indicated flattened private choice stream
and positive event signs. -/
def TraceRun {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (c : Code)
    (s : Bank w) (m : Memory w) (bits : List Bool) (budget : ℕ) (post : Bank w → Memory w → Prop) : Prop :=
  ∃ es t mt, Runs pub macros c s m es t mt ∧ TraceOK es bits es.length ∧ traceCost es ≤ budget ∧ post t mt

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
variable {a b c : Code} {s : Bank w} {m : Memory w} {bs cs : List Bool} {l k : ℕ}
variable {P Q : Bank w → Memory w → Prop}

/-- Append two actual executions, retaining all their choice bits. -/
theorem TraceRun.seq (r : TraceRun pub macros a s m bs l P)
    (next : ∀ t mt, P t mt → TraceRun pub macros b t mt cs k Q) :
    TraceRun pub macros (.seq a b) s m (bs++cs) (l+k) Q := by
  obtain ⟨es,t,mt,ra,ta,ca,hp⟩ := r
  obtain ⟨fs,z,mz,rb,tb,cb,hq⟩ := next t mt hp
  exact ⟨_,z,mz,ra.seq rb,by simpa only [List.length_append] using ta.append tb,
    (VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add ca cb),hq⟩

/-- Enlarge a tick budget and weaken the output condition. -/
theorem TraceRun.mono {v : ℕ} (r : TraceRun pub macros c s m bs k P) (h : k ≤ v)
    (post : ∀ t mt, P t mt → Q t mt) : TraceRun pub macros c s m bs v Q := by
  obtain ⟨es,t,mt,run,tr,cap,hp⟩ := r
  exact ⟨es,t,mt,run,tr,cap.trans h,post _ _ hp⟩

/-- An actual unsigned bounded execution contributes no private choices. -/
theorem traceRun_unsigned {post : NatState → Prop} (r : BoundedRun pub macros c s m k post)
    (h : c.unsigned = true) :
    TraceRun pub macros c s m [] k (fun t mt => post (.ofWords t mt)) := by
  obtain ⟨es,t,mt,run,cap,hp⟩ := r
  have fields := run.unsigned_events h
  refine ⟨es,t,mt,run,⟨rfl,?_,fun e he => (fields e he).2⟩,cap,hp⟩
  exact List.flatMap_eq_nil_iff.mpr fun e he => (fields e he).1

/-- A counted native loop concatenates exactly the per-iteration private words;
its physical time is the sum of the local bounds and the actual guard ticks. -/
theorem trace_counted (x y : Reg) (body : Code) (N : ℕ) (cost : ℕ → ℕ)
    (choices : ℕ → List Bool) (I : ℕ → Bank w → Memory w → Prop)
    (regs : ∀ i s m, I i s m → readings s x = i ∧ readings s y = N)
    (step : ∀ i < N, ∀ s m, I i s m → TraceRun pub macros body s m (choices i) (cost i) (I (i+1)))
    (i : ℕ) (hi : i ≤ N) (s : Bank w) (m : Memory w) (start : I i s m) :
    TraceRun pub macros (.whileLt x y body) s m ((List.range' i (N-i)).flatMap choices)
      ((∑ j ∈ Ico i N, (cost j+1))+1) (I N) := by
  obtain ⟨hx,hy⟩ := regs i s m start
  change (s x).val = i at hx
  change (s y).val = N at hy
  by_cases eqn : i = N
  · rw [eqn] at start ⊢
    refine ⟨_,s,m,Runs.whileDone (show ¬(s x).val < (s y).val by omega),?_,?_,start⟩
    · simp [TraceOK,tick]
    · simp [traceCost,tick,VPVNP.RAMBuckets.cost,TeamTranscript.Action.extra]
  · have lt : i < N := by omega
    obtain ⟨es,t,mt,r,tr,cap,hp⟩ := step i lt s m start
    obtain ⟨fs,z,mz,next,tr',cap',done⟩ := trace_counted x y body N cost choices I regs step
      (i+1) lt t mt hp
    refine ⟨_,z,mz,Runs.whileStep (show (s x).val < (s y).val by omega) r next,?_,?_,done⟩
    · rw [show N-i = (N-(i+1))+1 by omega, List.range'_succ]
      simpa only [List.flatMap_cons,List.length_cons,List.length_append] using (tr.append tr').cons_tick
    · change 1+traceCost (es++fs) ≤ _
      rw [show traceCost (es++fs) = traceCost es+traceCost fs from VPVNP.RAMBuckets.cost_append ..,
        sum_eq_sum_Ico_succ_bot lt]
      omega
termination_by N-i

/-- The guard at a chosen or skipped candidate adds one tick and no bit. -/
theorem TraceRun.branch {a b : Code} {x y : Reg}
    (h : TraceRun pub macros (if s x = s y then a else b) s m bs k P) :
    TraceRun pub macros (.ifEq x y a b) s m bs (1+k) P := by
  obtain ⟨es,t,mt,r,tr,cap,hp⟩ := h
  exact ⟨_,t,mt,Runs.ifEq r,tr.cons_tick,show 1+traceCost es ≤ _ from Nat.add_le_add_left cap _,hp⟩

end RoutingISA.Owned

end BorderVNP
end Computability
end OAI
