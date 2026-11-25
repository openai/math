import OAI.ThreeFlat.RAM.CountedProcedure
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI
/-! # Weighted total time for a native counted loop -/

namespace ThreeFlat.RAM.PhysicalProcedure.Procedure

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
open scoped BigOperators
variable {w : ℕ}

/-- A counted native loop charges the actual work of each site separately. -/
theorem counted_cost (body : Procedure w) (cell : Word w) (n : ℕ) (cost : ℕ→ℕ)
    (inv : ℕ → Memory w → Prop)
    (step : ∀ z m, inv (z+1) m → (m cell.val).val=z+1 →
      body.Spec (fun m' => m'=writeMemory m cell (m cell.val-1))
        (fun _ m' => (m' cell.val).val=z ∧ inv z m') (cost z)) :
    (body.counted cell).Spec (fun m => inv n m ∧ (m cell.val).val=n)
      (fun _ m' => inv 0 m') (4+7*n+∑ j ∈ Finset.range n,cost j) := by
  intro P R K M pc reg pub exit installed data c m entry initial
  let : NeZero (body.counted cell).labels := ⟨by change 7+body.labels≠0; omega⟩
  have root : (Fin.castAddEmb body.labels) (0 : Fin 7) = (0 : Fin (body.counted cell).labels) := by
    apply Fin.ext
    change (0 : Fin 7).val = (0 : Fin (body.counted cell).labels).val
    simp
  let inner := body.block.reindex (Fin.natAddEmb 3) id
  let ip := (Fin.natAddEmb 7).trans pc
  have rom : inner.Installed M ip reg pub (pc 0) := by
    intro i
    rw [show ip i = pc (Fin.natAdd 7 i) by rfl]
    have row := installed (Fin.natAdd 7 i)
    simp only [counted,CompressorIteration.block,Fin.addCases_right] at row
    exact row.trans (congrArg (fun stop => inner.emit ip reg pub stop i) (congrArg pc root))
  have nested := (body.block.reindex_installed (Fin.natAddEmb 3) id M ip reg pub (pc 0)).mp rom
  have run (z : ℕ) (q : Config w P R) (μ : Memory w) (hq : q.pc=pc 0) (hi : inv z μ) (count : (μ cell.val).val=z) :
      ∃ s≤4+7*z+∑ j ∈ Finset.range z,cost j, ∃ d out, advance M.program s q μ=some (d,out) ∧
        d.pc=exit ∧ inv 0 out := by
    induction z generalizing q μ with
    | zero =>
      obtain ⟨d,execute,atExit⟩ := (CompressorIteration.visit cell inner (Fin.castAddEmb body.registers) M
        pc reg pub exit installed q μ hq).1 (Fin.ext count)
      exact ⟨4,by simp,d,μ,execute,atExit,hi⟩
    | succ z ih =>
      have nonzero : μ cell.val≠0 := by intro eq; simp [eq] at count
      obtain ⟨d,t₁,begin⟩ := (CompressorIteration.visit cell inner (Fin.castAddEmb body.registers) M
        pc reg pub exit installed q μ hq).2 nonzero
      obtain ⟨t,ht,d',m',t₂,atGuard,next,ok⟩ := step z μ hi count M ip
        ((Fin.natAddEmb 3).trans reg) (pub ∘ id) (pc 0) nested data d _ begin rfl
      obtain ⟨s,hs,out,mem,t₃,atExit,done⟩ := ih d' m' atGuard ok next
      refine ⟨7+t+s,?_,out,mem,advance_trans (advance_trans t₁ t₂) t₃,atExit,done⟩
      rw [Nat.mul_succ,Finset.sum_range_succ]
      omega
  exact run n c m entry initial.1 initial.2

end ThreeFlat.RAM.PhysicalProcedure.Procedure

end OAI
