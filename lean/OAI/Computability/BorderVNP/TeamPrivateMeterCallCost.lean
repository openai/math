import OAI.Computability.BorderVNP.TeamPrivateMeterCall

/-! # Physical time for the trusted private clock, including resetting and cleaning its tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPrivateMeterCall

open TeamPrivateTape
variable {Q Γ : Type} {m g : ℕ}

private theorem cells_eq_sum (a : Alphabet Γ g) {v : ℕ} (ts : Fin v → SymbolTape Γ) :
    cells (tracks a ts) = ∑ i : Fin v, ∑ j : Fin g,
      (((ts i).track a j).left.length + ((ts i).track a j).right.length) := by
  unfold cells tracks
  rw [Fintype.sum_equiv finProdFinEquiv.symm _ (fun z : Fin v × Fin g =>
    ((ts z.1).track a z.2).left.length + ((ts z.1).track a z.2).right.length) (fun _ => rfl)]
  rw [Fintype.sum_prod_type]

/-- The initial tapes occupy at most one encoded input string and one encoded unary clock. -/
theorem timedInput_cells_le (M : TeamSite.Macro Q Γ m g) (mark : Γ) (bs : List Bool) (N : ℕ) :
    cells (timedInput M mark bs N) ≤ (N+bs.length)*g := by
  rw [timedInput,cells_eq_sum,Fin.sum_univ_succ]
  simp only [TeamPrivateTimeout.timedTapes,Fin.cons_zero,Fin.cons_succ]
  rw [← cells_eq_sum]
  have data := input_cells_le M.alphabet M.digit M.inputTape bs
  have timer : ∑ j : Fin g, (((TeamPrivateTimeout.meter M.alphabet.blank mark [] N).track M.alphabet j).left.length +
        ((TeamPrivateTimeout.meter M.alphabet.blank mark [] N).track M.alphabet j).right.length) ≤ N*g := by
    cases N <;> simp [TeamPrivateTimeout.meter,SymbolTape.track]
    nlinarith
  rw [Nat.add_mul]
  exact Nat.add_le_add timer data

/-- A uniform linear physical time bound in the actual burst, unary budget, and native steps. -/
theorem steps_le (M : TeamSite.Macro Q Γ m g) (mark : Γ) (bs : List Bool) (N : ℕ) {n choices out u}
    (native : TeamPrivateFragment.Run (trackTable M.alphabet (TeamPrivateTimeout.table M.alphabet.blank mark M.table))
      n M.start (timedInput M mark bs N) choices out u) :
    steps bs N n u ≤ (2*g+4)*bs.length + (2*g+9)*N + n*(3*((m+1)*g)+2) + 2*((m+1)*g)+10 := by
  have cleanup := TeamPrivateFragment.run_cost_le native
  have init := timedInput_cells_le M mark bs N
  have len : bs.tail.length ≤ bs.length := by simp
  have reset : N-1 ≤ N := Nat.sub_le ..
  have lenBound := Nat.mul_le_mul_left (g+4) len
  have resetBound := Nat.mul_le_mul_left (g+4) reset
  unfold steps TeamPrivateInput.steps TeamPrivateMeterReset.steps
  nlinarith

end TeamPrivateMeterCall

end BorderVNP
end Computability
end OAI
