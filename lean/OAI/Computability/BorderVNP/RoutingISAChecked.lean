import OAI.Computability.BorderVNP.RoutingISANatural

/-! # Reflection of read-only arithmetic and rejecting guards -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- Erase only rejecting checks in the arithmetic-fit test. The original
fragment still executes its rejection instructions. -/
def Code.relaxReject : Code → Code
  | .reject => .nop
  | .seq a b => .seq a.relaxReject b.relaxReject
  | .ifEq x y a b => .ifEq x y a.relaxReject b.relaxReject
  | .ifLt x y a b => .ifLt x y a.relaxReject b.relaxReject
  | c => c

/-- Erasing a guard leaves the register updates of the natural evaluator unchanged. -/
theorem Code.evalNat_relaxReject (c : Code) (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) :
    c.relaxReject.evalNat pub mem s = c.evalNat pub mem s := by
  induction c generalizing s <;> simp_all [Code.relaxReject, Code.evalNat]

/-- Successful executions of a fitted read-only fragment pass its actual
rejecting guards. The registers at every later guard are the registers reached
by the earlier physical instructions. -/
theorem Runs.checked {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s m es t mt} (run : Runs pub macros c s m es t mt) (det : c.deterministic = true)
    (fit : c.relaxReject.safeReadOnly w (readings pub) (readings m) (readings s)) :
    c.safeReadOnly w (readings pub) (readings m) (readings s) := by
  induction run with
  | @atom c s m a t sg bs atomic _ _ =>
    cases c <;> try contradiction
    all_goals exact fit
  | @seq a b s m es u mu fs t mt first second ih₁ ih₂ =>
    obtain ⟨da,db⟩ := Bool.and_eq_true_iff.mp det
    have h₁ := ih₁ da fit.1
    obtain ⟨gs,z,rz,_,hz⟩ := a.runReadOnly pub macros m s h₁
    obtain ⟨_,rfl,rfl⟩ := first.unique_of_deterministic da rz
    have h₂ := fit.2
    rw [Code.evalNat_relaxReject, ← hz] at h₂
    exact ⟨h₁,hz ▸ ih₂ db h₂⟩
  | @ifEq x y a b s m es t mt branch ih =>
    obtain ⟨da,db⟩ := Bool.and_eq_true_iff.mp det
    by_cases h : s x = s y
    · have hn : readings s x = readings s y := congrArg Fin.val h
      simp only [h, ite_true] at ih
      simp only [Code.safeReadOnly, hn, ite_true]
      apply ih da
      simpa only [Code.relaxReject, Code.safeReadOnly, hn, ite_true] using fit
    · have hn : readings s x ≠ readings s y := fun e => h (Fin.ext e)
      simp only [h, ite_false] at ih
      simp only [Code.safeReadOnly, hn, ite_false]
      apply ih db
      simpa only [Code.relaxReject, Code.safeReadOnly, hn, ite_false] using fit
  | @ifLt x y a b s m es t mt branch ih =>
    obtain ⟨da,db⟩ := Bool.and_eq_true_iff.mp det
    by_cases h : s x < s y
    · have hn : readings s x < readings s y := h
      simp only [h, ite_true] at ih
      simp only [Code.safeReadOnly, hn, ite_true]
      apply ih da
      simpa only [Code.relaxReject, Code.safeReadOnly, hn, ite_true] using fit
    · have hn : ¬ readings s x < readings s y := h
      simp only [h, ite_false] at ih
      simp only [Code.safeReadOnly, hn, ite_false]
      apply ih db
      simpa only [Code.relaxReject, Code.safeReadOnly, hn, ite_false] using fit
  | choose | whileDone | whileStep => exact fit.elim

end RoutingISA

end BorderVNP
end Computability
end OAI
