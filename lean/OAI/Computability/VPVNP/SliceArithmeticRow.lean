import OAI.Computability.VPVNP.SliceArithmeticWord

/-!
# One coefficient of a Horner round on bit stacks

The evaluator computes the shifted predecessor plus two scalar products.
It uses registers 0 through 5 for the modulus, predecessor, negated top
coefficient, modulus coefficient, Horner digit and multiplier coefficient,
respectively. Register 6 receives the result and register 7 holds the second
product. The same control works at every coefficient and every word width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmeticRow

open BurstRAM PrivateRAM RAMTape ISA
open SliceArithmetic.Word

/-- Execute the four modular operations for one Horner coefficient, leaving its result in
register six. -/
def row {k : ℕ} : FiniteRoutine (Port 8 k) :=
  (((routine .mul 6 2 3 0).followedBy (routine .add 6 1 6 0)).followedBy
    (routine .mul 7 4 5 0)).followedBy (routine .add 6 6 7 0)

/-- The two destination registers at the end of a row calculation. -/
def rowRegisters {p w : ℕ} (reg : Fin 8 → BurstRAM.Word w)
    (prev reduction c digit b : Fin p) : Fin 8 → BurstRAM.Word w :=
  Function.update (Function.update reg 7 (limb w (digit * b))) 6
    (limb w (prev + reduction * c + digit * b))

theorem row_runs {p k w : ℕ} [NeZero p] (hw : workingWidth p ≤ w)
    (pub : Fin k → BurstRAM.Word w) (persistent : BurstRAM.Word w)
    (reg : Fin 8 → BurstRAM.Word w) (log : WriteLog w) (prev reduction c digit b : Fin p)
    (hp : (reg 0).val = p) (hprev : (reg 1).val = prev.val)
    (hred : (reg 2).val = reduction.val) (hc : (reg 3).val = c.val)
    (hd : (reg 4).val = digit.val) (hb : (reg 5).val = b.val) :
    ∃ t ≤ 800 * (w + 1) ^ 2, row.Runs t (bank pub persistent reg log)
      (bank pub persistent (rowRegisters reg prev reduction c digit b) log) := by
  let r₁ := Function.update reg 6 (limb w (reduction * c))
  let r₂ := Function.update r₁ 6 (limb w (prev + reduction * c))
  let r₃ := Function.update r₂ 7 (limb w (digit * b))
  obtain ⟨t₁, ht₁, run₁⟩ := routine_runs hw .mul 6 2 3 0 (by decide) pub persistent reg log
    reduction c hred hc hp
  obtain ⟨t₂, ht₂, run₂⟩ := routine_runs hw .add 6 1 6 0 (by decide) pub persistent r₁ log
    prev (reduction * c) (by simpa [r₁] using hprev) (by simp [r₁, limb_val hw])
    (by simpa [r₁] using hp)
  obtain ⟨t₃, ht₃, run₃⟩ := routine_runs hw .mul 7 4 5 0 (by decide) pub persistent r₂ log
    digit b (by simpa [r₂, r₁] using hd) (by simpa [r₂, r₁] using hb) (by simpa [r₂, r₁] using hp)
  obtain ⟨t₄, ht₄, run₄⟩ := routine_runs hw .add 6 6 7 0 (by decide) pub persistent r₃ log
    (prev + reduction * c) (digit * b)
    (by simp [r₃, r₂, limb_val hw]) (by simp [r₃, limb_val hw]) (by simpa [r₃, r₂, r₁] using hp)
  have heq : Function.update r₃ 6 (limb w (prev + reduction * c + digit * b)) =
      rowRegisters reg prev reduction c digit b := by
    funext i
    by_cases h6 : i = 6 <;> by_cases h7 : i = 7 <;>
      simp [r₃, r₂, r₁, rowRegisters, h6, h7]
  simp only [Op.eval] at run₄
  rw [heq] at run₄
  exact ⟨_, by omega, ((run₁.followedBy run₂).followedBy run₃).followedBy run₄⟩

end SliceArithmeticRow

end VPVNP
end Computability
end OAI
