import OAI.Computability.VPVNP.RAMTapePrivateISAKernels
import OAI.Computability.VPVNP.RAMTapeISAOperand

/-!
# A private store on the architectural stack bank

The instruction copies the address and the value from the architectural
registers, prepends their bits to the private log, and clears the two staging
ports. Since each operand copy restores its source, one register may supply
both operands.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ISA

open BurstRAM PrivateRAM

variable {w r k : ℕ}

/-- Execute the private store with its two source registers fixed by the
instruction table. -/
def storePrivate (addr src : Fin r) : FiniteRoutine (Port r k) :=
  (loadOperand (.reg addr) (.logPort .query)).followedBy <|
    (loadOperand (.reg src) (.logPort .out)).followedBy <|
      logStore.followedBy <|
        (clearPort (.logPort .query)).followedBy (clearPort (.logPort .out))

/-- The newest write extends the private log and the instruction returns
with an empty workspace. The instruction count is independent of the old
log length and of the address stored in the register. -/
theorem storePrivate_run (addr src : Fin r) (pub : Fin k → Word w) (persistent : Word w)
    (reg : Fin r → Word w) (log : WriteLog w) :
    (storePrivate (k := k) addr src).Runs (26 * w + 11)
      (bank pub persistent reg log)
      (bank pub persistent reg ((reg addr, reg src) :: log)) := by
  let a := reg addr
  let v := reg src
  let after := (a, v) :: log
  let staged := stagedBank pub persistent reg
  have h₁ := loadOperand_runs (src := Port.reg addr) (dst := .logPort .query)
    (by simp) (by simp [copySafe]) (by simp [copySafe]) (staged log [] []) rfl rfl
  change (loadOperand _ _).Runs (0 + 7 * (wordBits a).length + 3) (staged log [] [])
    (Function.update (staged log [] []) (.logPort .query) (wordBits a)) at h₁
  simp only [staged, stagedBank_update_query, Nat.zero_add, length_wordBits] at h₁
  have h₂ := loadOperand_runs (src := Port.reg src) (dst := .logPort .out)
    (by simp) (by simp [copySafe]) (by simp [copySafe]) (staged log (wordBits a) []) rfl rfl
  change (loadOperand _ _).Runs (0 + 7 * (wordBits v).length + 3) (staged log (wordBits a) [])
    (Function.update (staged log (wordBits a) []) (.logPort .out) (wordBits v)) at h₂
  simp only [staged, stagedBank_update_out, Nat.zero_add, length_wordBits] at h₂
  have h₃ := logStore_run pub persistent reg log a v
  have h₄ := clearPort_runs (Port.logPort .query) (staged after (wordBits a) (wordBits v))
  change (clearPort _).Runs ((wordBits a).length + 1) _
    (Function.update (staged after (wordBits a) (wordBits v)) (.logPort .query) []) at h₄
  simp only [staged, stagedBank_update_query, length_wordBits] at h₄
  have h₅ := clearPort_runs (Port.logPort .out) (staged after [] (wordBits v))
  change (clearPort _).Runs ((wordBits v).length + 1) _
    (Function.update (staged after [] (wordBits v)) (.logPort .out) []) at h₅
  simp only [staged, stagedBank_update_out, length_wordBits] at h₅
  have run := h₁.followedBy (h₂.followedBy (h₃.followedBy (h₄.followedBy h₅)))
  rw [show 7 * w + 3 + (7 * w + 3 + (10 * w + 3 + (w + 1 + (w + 1)))) = 26 * w + 11 by omega] at run
  simpa only [stagedBank_empty, storePrivate] using run

end RAMTape.ISA

end VPVNP
end Computability
end OAI
