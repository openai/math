import OAI.Computability.BorderVNP.RoutingISATableState
import OAI.Computability.BorderVNP.RoutingISADeterministic
import OAI.Computability.BorderVNP.RoutingISACallInversion
import Mathlib.Algebra.BigOperators.Intervals

/-! # Exact tests with nonuniform per-iteration costs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM Finset

/-- A checked fragment returns precisely when its stated test succeeds. Every
returned path satisfies the postcondition, and successful tests have a path
within the specified tick allowance. -/
structure TestRun {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (c : Code) (s : Bank w) (m : Memory w) (cost : ℕ) (ok : Prop)
    (post : NatState → Prop) : Prop where
  /-- Completeness with the actual traced cost. -/
  complete : ok → BoundedRun pub macros c s m cost post
  /-- Converse on arbitrary returning runs. -/
  sound {es t mt} : Runs pub macros c s m es t mt → ok ∧ post (.ofWords t mt)

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8} {c a b : Code}
  {s : Bank w} {m : Memory w} {cost ca cb : ℕ} {ok oa ob : Prop} {P Q : NatState → Prop}

/-- A bounded deterministic return can be used as an unconditional stage. -/
theorem BoundedRun.asTest (run : BoundedRun pub macros c s m cost P) (hd : c.deterministic = true) :
    TestRun pub macros c s m cost True P := by
  refine ⟨fun _ => run, ?_⟩
  obtain ⟨gs,u,mu,actual,_,hp⟩ := run
  intro es t mt other
  obtain ⟨_,rfl,rfl⟩ := other.unique_of_deterministic hd actual
  exact ⟨trivial,hp⟩

/-- Join two consecutive tests and add their physical costs. -/
theorem TestRun.seq (first : TestRun pub macros a s m ca oa P)
    (second : ∀ t mt, P (.ofWords t mt) → TestRun pub macros b t mt cb ob Q) :
    TestRun pub macros (.seq a b) s m (ca+cb) (oa ∧ ob) Q := by
  refine ⟨fun ho => (first.complete ho.1).seq (fun t mt h => (second t mt h).complete ho.2),?_⟩
  intro es t mt run
  cases run with
  | atom ha _ _ => cases ha
  | seq r r' =>
    obtain ⟨left,h⟩ := first.sound r
    obtain ⟨right,h'⟩ := (second _ _ h).sound r'
    exact ⟨⟨left,right⟩,h'⟩

/-- Relax the budget, identify the success predicate, and weaken the final state. -/
theorem TestRun.mono {cost' : ℕ} {ok' : Prop} (h : TestRun pub macros c s m cost ok P)
    (fit : cost ≤ cost') (test : ok ↔ ok') (weaken : ∀ z, P z → Q z) :
    TestRun pub macros c s m cost' ok' Q :=
  ⟨fun good => (h.complete (test.mpr good)).mono fit weaken, fun r =>
    ⟨test.mp (h.sound r).1, weaken _ (h.sound r).2⟩⟩

/-- A counted loop with rejecting body tests validates every index in its
half-open interval. Its allowance sums the individual index costs. -/
theorem test_counted_loop (x y : Reg) (body : Code) (N : ℕ) (cost : ℕ → ℕ)
    (good : ℕ → Prop) (I : ℕ → NatState → Prop)
    (regs : ∀ i z, I i z → z.reg x = i ∧ z.reg y = N)
    (step : ∀ i < N, ∀ t mt, I i (.ofWords t mt) →
      TestRun pub macros body t mt (cost i) (good i) (I (i+1)))
    (i : ℕ) (hi : i ≤ N) (s : Bank w) (m : Memory w) (hs : I i (.ofWords s m)) :
    TestRun pub macros (.whileLt x y body) s m ((∑ j ∈ Ico i N, (cost j + 1)) + 1)
      (∀ j, i ≤ j → j < N → good j) (I N) := by
  obtain ⟨hx,hy⟩ := regs _ _ hs
  change (s x).val = i at hx
  change (s y).val = N at hy
  by_cases h : i = N
  · rw [h] at hs hx ⊢
    have hg : ¬ s x < s y := show ¬ (s x).val < (s y).val by omega
    refine ⟨fun _ => ⟨_,s,m,Runs.whileDone hg,by simp [traceCost,tick,VPVNP.RAMBuckets.cost,
      TeamTranscript.Action.extra],hs⟩,?_⟩
    intro es t mt run
    obtain ⟨_,rfl,rfl⟩ := CellDispatch.while_last run hg
    exact ⟨fun j lo high => (not_lt.mpr lo high).elim,hs⟩
  · have lt : i < N := by omega
    have hg : s x < s y := show (s x).val < (s y).val by omega
    have first := step i lt s m hs
    have next t mt (hn : I (i+1) (.ofWords t mt)) := test_counted_loop x y body N cost good I
      regs step (i+1) lt t mt hn
    constructor
    · intro checks
      obtain ⟨es,t,mt,run,cap,hn⟩ := first.complete (checks i le_rfl lt)
      obtain ⟨fs,z,mz,tail,cap',post⟩ := (next t mt hn).complete (fun j lo hi => checks j (by omega) hi)
      refine ⟨_,z,mz,Runs.whileStep hg run tail,?_,post⟩
      change 1 + traceCost (es ++ fs) ≤ _
      rw [show traceCost (es ++ fs) = traceCost es + traceCost fs from VPVNP.RAMBuckets.cost_append ..,
        Finset.sum_eq_sum_Ico_succ_bot lt]
      omega
    · intro es t mt run
      obtain ⟨gs,z,mz,fs,_,r,r'⟩ := CellDispatch.while_next run hg
      obtain ⟨pass,hn⟩ := first.sound r
      obtain ⟨rest,post⟩ := (next z mz hn).sound r'
      exact ⟨fun j lo hi => (Nat.eq_or_lt_of_le lo).elim (fun he => he ▸ pass) (fun h' => rest j h' hi),post⟩
termination_by N-i

end RoutingISA

end BorderVNP
end Computability
end OAI
