import OAI.Computability.VPVNP.PairSimulationLeafImageHandler

/-! # Per-leaf instruction and probe bounds at the actual auxiliary cutoff -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.StackMachine

open BurstRAM RAMTape

variable {K Q : Type} [DecidableEq K] {w : ℕ}

/-- A missing choice, failed halt, or expired source clock also respects
the same native transition bound. -/
theorem footprint_length_le (L : Layout K w) (code : StackCode K Q) (fuel : ℕ)
    (q : Q) (s : Stacks K) (bits : List Bool) :
    (footprint L code fuel q s bits).events.length ≤ 4*fuel := by
  induction fuel generalizing q s bits with
  | zero => rfl
  | succ fuel ih =>
    cases h : code q with
    | push | pop | goto =>
      simp only [footprint,h,Footprint.prepend,List.length_append,List.length_replicate,Nat.mul_succ]
      exact Nat.add_le_add_left (ih ..) _ |>.trans_eq (Nat.add_comm ..)
    | choose lo hi =>
      cases bits with
      | nil => simp only [footprint,h,List.length_replicate,Nat.mul_succ]; omega
      | cons b bs =>
        simp only [footprint,h,Footprint.prepend,List.length_append,List.length_cons,List.length_nil,Nat.mul_succ]
        have := ih (if b then hi else lo) s bs; omega
    | halt b => cases b <;> simp [footprint,h,Nat.mul_succ]

end PairSimulation.StackMachine

namespace PairSimulation.LeafVisit

open BurstRAM PrivateRAM CursorNetwork CursorRouting LeafHandler LeafStartup DFS Filter
open scoped Fin.CommRing

variable {w p r k : ℕ} {A : PrimedInputRAM.Lengths} {n a H s : ℕ}
    {Q : PrimedInputRAM.Layout A n a H w} (D : PrimedCounter.Data Q s)
    {b l e endAddr : ℕ} [NeZero (b+l)] (budget : ProcessorBudget n (b+l) e w)
    (R : LeafArena.Regions) (fit : R.stackBase + Fintype.card ScalarPort*n^40 < 2^w)
    {M : Machine w p r k} (pub : LeafImage.Pub → Fin k) (m : Memory w)

private theorem tick_probes (n : ℕ) : countProbes (List.replicate n (.tick : Event w)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,countProbes,ih]

theorem trace_probes (f : LeafAddress.Field → Word w) (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w) :
    countProbes (trace D budget m f v buf) ≤ 1 := by
  rw [trace,countProbes_append,LeafFront.trace_probes]
  by_cases hz : v.1=0
  · rw [ite_eq_left hz,tick_probes]
    cases decide ((v.2.val : Word w) < f .span) <;> decide
  · rw [ite_eq_right hz,show countProbes ([] : List (Event w)) = 0 from rfl]
    cases decide ((v.2.val : Word w) < f .span) <;> decide

theorem trace_length (f : LeafAddress.Field → Word w) (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w)
    (hn : 2048 ≤ n) (cost : LeafBoot.ticks D budget.tags budget.capFits v.2 buf ≤ n^15) :
    (trace D budget m f v buf).length ≤ n^16 := by
  have hroute := (RouteSchedule.routeTicks_le w v (2^e) w).trans (RouteSchedule.clock_le budget hn)
  have h₁ : 1 ≤ n := by omega
  have h₅ := Nat.pow_le_pow_right h₁ (by decide : 5 ≤ 15)
  have hbig : 60*n^15 ≤ n^16 := by rw [pow_succ' n 15]; exact Nat.mul_le_mul_right _ (by omega)
  have := Nat.one_le_pow 15 n h₁
  rw [trace,List.length_append,(LeafFront.trace_cost ..).1]
  simp only [RoutePrepare.ticks]
  split <;> simp only [List.length_replicate,List.length_nil] <;> omega

/-- Room for the native role dispatch and its operand reload is included in
the private-work estimate. Only the translated virtual header may probe
external memory inside this leaf. -/
theorem parser_work (hn : 2048 ≤ n)
    (boot : ∀ (v : Site (b+l)) (buf : Buffers (b+l) (2^e) w),
      LeafBoot.ticks D budget.tags budget.capFits v buf ≤ n^15)
    (node : Word w) (saved : Scratch w endAddr) (bits : List Bool) {job : VisitPath w endAddr} {tail : List Bool}
    (read : (leafParser (M := M) D budget R fit pub m (n^39)).read node saved bits = some (job,tail)) :
    countProbes job.trace ≤ 1 ∧ job.trace.length + 47 ≤ n^40 := by
  let f := fields (M := M) pub
  let v := physicalPosition (b+l) f node
  let buf := physicalBuffers (b+l) (2^e) w R.arguments node saved
  obtain ⟨probes,cost⟩ := LeafHandler.parser_work D budget.tags budget.capFits (storage R fit)
    (loaded D budget R fit f m) (n^39) node saved bits read
  refine ⟨probes.trans_le (trace_probes D budget m f v buf),?_⟩
  have t := trace_length D budget m f v buf hn (boot v.2 buf)
  change job.trace.length ≤ (trace D budget m f v buf).length+4*n^39 at cost
  have h₁ : 1 ≤ n := by omega
  have h₁₆ := Nat.pow_le_pow_right h₁ (by decide : 16 ≤ 39)
  have := Nat.one_le_pow 39 n h₁
  have cap : 52*n^39 ≤ n^40 := by rw [pow_succ' n 39]; exact Nat.mul_le_mul_right _ (by omega)
  omega

/-- Include the complete compiled prefix and interpreter's event counts
even when the stack computation rejects or its input tape ends early. -/
theorem malformed_work (hn : 2048 ≤ n) (f : LeafAddress.Field → Word w)
    (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w) (bits : List Bool)
    (boot : LeafBoot.ticks D budget.tags budget.capFits v.2 buf ≤ n^15) :
    let head := trace D budget m f v buf
    let body := StackMachine.footprint (storage R fit) auxiliaryCode (n^39) auxiliaryEntry
      (auxiliaryBank D budget.tags budget.capFits v buf) bits
    countProbes (head ++ body.events) ≤ 1 ∧ (head ++ body.events).length + 47 ≤ n^40 := by
  intro head body
  rw [countProbes_append,StackMachine.footprint_probes,Nat.add_zero,List.length_append]
  refine ⟨trace_probes D budget m f v buf,?_⟩
  have ht : head.length ≤ n^16 := trace_length D budget m f v buf hn boot
  have hb : body.events.length ≤ 4*n^39 := StackMachine.footprint_length_le ..
  have h₁ : 1 ≤ n := by omega
  have h₁₆ := Nat.pow_le_pow_right h₁ (by decide : 16 ≤ 39)
  have := Nat.one_le_pow 39 n h₁
  have cap : 52*n^39 ≤ n^40 := by rw [pow_succ' n 39]; exact Nat.mul_le_mul_right _ (by omega)
  omega

end PairSimulation.LeafVisit

end VPVNP
end Computability
end OAI
