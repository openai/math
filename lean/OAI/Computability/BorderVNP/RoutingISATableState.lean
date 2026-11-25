import OAI.Computability.BorderVNP.RoutingISANatural
import OAI.Computability.BorderVNP.RoutingISATable

/-! # Straight-line natural semantics for the scheduling table

The scheduler writes memory in its loop bodies. The pair of register and memory
functions here records the result of every store. The guard for each arithmetic
instruction checks its actual operands before using the unsigned word operation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Unbounded natural readings of a register bank and its addressed shared memory. -/
structure NatState where
  /-- All 64 register values. -/
  reg : Reg → ℕ
  /-- Value at each shared-memory address. -/
  mem : ℕ → ℕ

/-- Read the physical words into the natural state. -/
def NatState.ofWords {w : ℕ} (s : Bank w) (m : Memory w) : NatState :=
  ⟨readings s, readings m⟩

/-- Natural state returned by a straight-line block with conditional branches and stores. -/
def Code.fixedEval (pub : Arg → ℕ) : Code → NatState → NatState
  | .seq a b, s => b.fixedEval pub (a.fixedEval pub s)
  | .ifLt x y a b, s => if s.reg x < s.reg y then a.fixedEval pub s else b.fixedEval pub s
  | .ifEq x y a b, s => if s.reg x = s.reg y then a.fixedEval pub s else b.fixedEval pub s
  | .store a v, s => ⟨s.reg, Function.update s.mem (s.reg a) (s.reg v)⟩
  | c, s => ⟨c.evalNat pub s.mem s.reg, s.mem⟩

/-- Every register below the protected boundary survives all conditional paths, including
paths with writes to shared memory. -/
theorem Code.fixedEval_protected (c : Code) (pub : Arg → ℕ) (z : NatState) {lo : ℕ}
    (hc : c.protects lo = true) (j : Reg) (hj : j.val < lo) :
    (c.fixedEval pub z).reg j = z.reg j := by
  induction c generalizing z with
  | seq a b iha ihb =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hc
    exact (ihb _ hb).trans (iha z ha)
  | ifEq x y a b iha ihb | ifLt x y a b iha ihb =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hc
    simp only [Code.fixedEval]
    split
    · exact iha _ ha
    · exact ihb _ hb
  | store => rfl
  | _ => exact Code.evalNat_protected _ pub z.mem z.reg hc j hj

/-- No rejection, overflow or unsupported instruction on the taken straight-line path. -/
def Code.fixedSafe (w : ℕ) (pub : Arg → ℕ) : Code → NatState → Prop
  | .seq a b, s => a.fixedSafe w pub s ∧ b.fixedSafe w pub (a.fixedEval pub s)
  | .ifLt x y a b, s => if s.reg x < s.reg y then a.fixedSafe w pub s else b.fixedSafe w pub s
  | .ifEq x y a b, s => if s.reg x = s.reg y then a.fixedSafe w pub s else b.fixedSafe w pub s
  | .store .., _ => True
  | c, s => c.safeReadOnly w pub s.mem s.reg

/-- Bounded native execution reaching a postcondition on the full physical state. -/
def BoundedRun {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (c : Code)
    (s : Bank w) (m : Memory w) (bound : ℕ) (post : NatState → Prop) : Prop :=
  ∃ es t mt, Runs pub macros c s m es t mt ∧ traceCost es ≤ bound ∧ post (.ofWords t mt)

private theorem ofWords_update_mem {w : ℕ} (s : Bank w) (m : Memory w) (a : ℕ) (v : Word w) :
    NatState.ofWords s (Function.update m a v) =
      ⟨readings s, Function.update (readings m) a v.val⟩ := by
  apply congrArg (NatState.mk (readings s))
  funext i
  by_cases h : i = a <;> simp [readings, h]

/-- Every safe straight-line path of the natural evaluator executes at word width
`w` with the exact final register and memory readings. -/
theorem Code.runFixed {w : ℕ} (c : Code) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (safe : c.fixedSafe w (readings pub) (.ofWords s m)) :
    BoundedRun pub macros c s m c.slots (· = c.fixedEval (readings pub) (.ofWords s m)) := by
  induction c generalizing s m with
  | seq a b iha ihb =>
    obtain ⟨es,t,mt,ra,ha,he⟩ := iha s m safe.1
    obtain ⟨fs,u,mu,rb,hb,hf⟩ := ihb t mt (he ▸ safe.2)
    refine ⟨_,u,mu,ra.seq rb,(VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add ha hb),?_⟩
    simpa only [Code.fixedEval, ← he] using hf
  | ifLt x y a b iha ihb =>
    by_cases h : s x < s y
    · have h' : (NatState.ofWords s m).reg x < (NatState.ofWords s m).reg y := h
      obtain ⟨es,t,mt,r,hc,he⟩ := iha s m (by simpa [Code.fixedSafe,h'] using safe)
      refine ⟨_,_,_,Runs.ifLt (by simpa [h] using r),?_,by simpa [fixedEval,h'] using he⟩
      change 1+traceCost es ≤ 1+a.slots+b.slots
      omega
    · have h' : ¬ (NatState.ofWords s m).reg x < (NatState.ofWords s m).reg y := h
      obtain ⟨es,t,mt,r,hc,he⟩ := ihb s m (by simpa [Code.fixedSafe,h'] using safe)
      refine ⟨_,_,_,Runs.ifLt (by simpa [h] using r),?_,by simpa [fixedEval,h'] using he⟩
      change 1+traceCost es ≤ 1+a.slots+b.slots
      omega
  | ifEq x y a b iha ihb =>
    by_cases h : s x = s y
    · have h' : (NatState.ofWords s m).reg x = (NatState.ofWords s m).reg y := congrArg Fin.val h
      obtain ⟨es,t,mt,r,hc,he⟩ := iha s m (by simpa [fixedSafe,h'] using safe)
      refine ⟨_,_,_,Runs.ifEq (by simpa [h] using r),?_,by simpa [fixedEval,h'] using he⟩
      change 1+traceCost es ≤ 1+a.slots+b.slots
      omega
    · have h' : (NatState.ofWords s m).reg x ≠ (NatState.ofWords s m).reg y := fun e => h (Fin.ext e)
      obtain ⟨es,t,mt,r,hc,he⟩ := ihb s m (by simpa [fixedSafe,h'] using safe)
      refine ⟨_,_,_,Runs.ifEq (by simpa [h] using r),?_,by simpa [fixedEval,h'] using he⟩
      change 1+traceCost es ≤ 1+a.slots+b.slots
      omega
  | store a v => exact ⟨_,_,_,Runs.store pub macros a v s m,le_rfl,ofWords_update_mem ..⟩
  | nop | constant | publicWord | copy | binary | load =>
    obtain ⟨es,t,r,hc,he⟩ := Code.runReadOnly _ pub macros m s safe
    exact ⟨es,t,m,r,hc,congrArg (fun z => NatState.mk z (readings m)) he⟩
  | _ => exact safe.elim

/-- Sequencing bounded executions adds the two time allowances. -/
theorem BoundedRun.seq {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {a b : Code} {s : Bank w} {m : Memory w} {v t : ℕ} {P Q : NatState → Prop}
    (first : BoundedRun pub macros a s m v P)
    (next : ∀ u mu, P (.ofWords u mu) → BoundedRun pub macros b u mu t Q) :
    BoundedRun pub macros (.seq a b) s m (v+t) Q := by
  obtain ⟨es,u,mu,r,hr,hp⟩ := first
  obtain ⟨fs,z,mz,r',hr',hq⟩ := next u mu hp
  exact ⟨_,z,mz,r.seq r',(VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add hr hr'),hq⟩

/-- Weaken a postcondition or enlarge the allowed tick budget. -/
theorem BoundedRun.mono {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s : Bank w} {m : Memory w} {v t : ℕ} {P Q : NatState → Prop}
    (run : BoundedRun pub macros c s m v P) (hb : v ≤ t) (hq : ∀ z, P z → Q z) :
    BoundedRun pub macros c s m t Q := by
  obtain ⟨es,u,mu,r,hc,hp⟩ := run
  exact ⟨es,u,mu,r,hc.trans hb,hq _ hp⟩

/-- A native counted loop consumes one guard tick per iteration and one final guard tick.
The supplied invariant includes the actual counter and bound registers at every stage. -/
theorem run_counted_loop {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (x y : Reg) (body : Code) (N cost : ℕ) (P : ℕ → NatState → Prop)
    (regs : ∀ i z, P i z → z.reg x = i ∧ z.reg y = N)
    (step : ∀ i < N, ∀ s m, P i (.ofWords s m) → BoundedRun pub macros body s m cost (P (i+1)))
    (i : ℕ) (hi : i ≤ N) (s : Bank w) (m : Memory w) (hp : P i (.ofWords s m)) :
    BoundedRun pub macros (.whileLt x y body) s m ((N-i)*(cost+1)+1) (P N) := by
  obtain ⟨hx,hy⟩ := regs i _ hp
  change (s x).val = i at hx
  change (s y).val = N at hy
  by_cases h : i = N
  · rw [h] at hp ⊢
    exact ⟨_,s,m,Runs.whileDone (show ¬ (s x).val < (s y).val by omega),by simp [traceCost,tick,
      VPVNP.RAMBuckets.cost,TeamTranscript.Action.extra],hp⟩
  · have hlt : i < N := by omega
    obtain ⟨es,u,mu,r,hc,hq⟩ := step i hlt s m hp
    obtain ⟨fs,z,mz,r',hc',hp'⟩ := run_counted_loop pub macros x y body N cost P regs step
      (i+1) hlt u mu hq
    refine ⟨_,z,mz,Runs.whileStep (show (s x).val < (s y).val by omega) r r',?_,hp'⟩
    change 1 + traceCost (es ++ fs) ≤ _
    rw [show traceCost (es ++ fs) = traceCost es + traceCost fs from VPVNP.RAMBuckets.cost_append ..]
    have he : N-i = (N-(i+1))+1 := by omega
    rw [he, Nat.add_mul, one_mul]
    omega
termination_by N-i

end RoutingISA

end BorderVNP
end Computability
end OAI
