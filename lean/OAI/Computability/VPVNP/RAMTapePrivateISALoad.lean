import OAI.Computability.VPVNP.RAMTapePrivateISAKernels
import OAI.Computability.VPVNP.RAMTapeISAOperand

/-!
# Lowering the private-load opcode to finite stack control

The first copy stages the complete address before the destination register is
overwritten. This also implements loads whose address and destination are the
same register. The write log is restored by its kernel and the two staging
ports are emptied before returning to the instruction dispatcher.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ISA

open BurstRAM PrivateRAM

variable {r k w p : ℕ}

/-- Stage the address before overwriting the destination, look it up in the private write log,
copy the result to the destination, and clear both staging stacks. -/
def loadPrivate (dst addr : Fin r) : FiniteRoutine (Port r k) :=
  (((loadOperand (.reg addr) (.logPort .query)).followedBy logLoad).followedBy
    (loadOperand (.logPort .out) (.reg dst))).followedBy
      ((clearPort (.logPort .query)).followedBy (clearPort (.logPort .out)))

theorem loadPrivate_run (dst addr : Fin r) (pub : Fin k → Word w) (s : Word w)
    (reg : Fin r → Word w) (log : WriteLog w) :
    (loadPrivate dst addr).Runs (17*w + 8 + AddressLog.loadCost (reg addr) log)
      (bank pub s reg log) (bank pub s (Function.update reg dst (WriteLog.memory log (reg addr))) log) := by
  let a := reg addr
  let v := WriteLog.memory log a
  let reg' := Function.update reg dst v
  let stage := stagedBank pub s reg log
  let post := stagedBank pub s reg' log
  have address : (loadOperand (.reg addr) (.logPort .query)).Runs (7*w+3)
      (stage [] []) (stage (wordBits a) []) := by
    have h := loadOperand_runs (src := .reg addr) (dst := .logPort .query)
      (by simp) (by simp [copySafe]) (by simp [copySafe]) (stage [] []) rfl rfl
    change (loadOperand _ _).Runs (0 + 7*(wordBits a).length + 3) _
      (Function.update (stagedBank pub s reg log [] []) (.logPort .query) (wordBits a)) at h
    simpa only [Nat.zero_add, length_wordBits, stagedBank_update_query] using h
  have readValue : logLoad.Runs (AddressLog.loadCost a log) (stage (wordBits a) [])
      (stage (wordBits a) (wordBits v)) := logLoad_run pub s reg log a
  have writeReg : (loadOperand (.logPort .out) (.reg dst)).Runs (8*w+3)
      (stage (wordBits a) (wordBits v)) (post (wordBits a) (wordBits v)) := by
    have h := loadOperand_runs (src := .logPort .out) (dst := .reg dst)
      (by simp) (by simp [copySafe]) (by simp [copySafe]) (stage (wordBits a) (wordBits v)) rfl rfl
    change (loadOperand _ _).Runs ((wordBits (reg dst)).length + 7*(wordBits v).length + 3) _
      (Function.update (stagedBank pub s reg log (wordBits a) (wordBits v)) (.reg dst) (wordBits v)) at h
    rw [stagedBank_update_reg, length_wordBits, length_wordBits] at h
    exact (show w + 7*w + 3 = 8*w + 3 by omega) ▸ h
  have clearAddress : (clearPort (.logPort .query)).Runs (w+1)
      (post (wordBits a) (wordBits v)) (post [] (wordBits v)) := by
    have h := clearPort_runs (.logPort .query) (post (wordBits a) (wordBits v))
    change (clearPort _).Runs ((wordBits a).length + 1) _
      (Function.update (stagedBank pub s reg' log (wordBits a) (wordBits v)) (.logPort .query) []) at h
    simpa only [length_wordBits, stagedBank_update_query] using h
  have clearValue : (clearPort (.logPort .out)).Runs (w+1) (post [] (wordBits v)) (post [] []) := by
    have h := clearPort_runs (.logPort .out) (post [] (wordBits v))
    change (clearPort _).Runs ((wordBits v).length + 1) _
      (Function.update (stagedBank pub s reg' log [] (wordBits v)) (.logPort .out) []) at h
    simpa only [length_wordBits, stagedBank_update_out] using h
  have h := ((address.followedBy readValue).followedBy writeReg).followedBy (clearAddress.followedBy clearValue)
  rw [show (7*w+3+AddressLog.loadCost a log+(8*w+3))+(w+1+(w+1)) =
    17*w+8+AddressLog.loadCost a log by omega] at h
  simpa only [loadPrivate, stage, post, reg', a, v, stagedBank_empty] using h

/-- For an arbitrary private configuration the physical load realizes the
exact private continuation of the opcode. -/
theorem loadPrivate_config_run (dst addr : Fin r) (next : Fin p) (pub : Fin k → Word w)
    (c : LogConfig w p r) :
    ∃ c' : LogConfig w p r,
      (Instr.loadPrivate dst addr next).runLogged pub c = .localStep c' ∧
      (loadPrivate dst addr).Runs (17*w + 8 + AddressLog.loadCost (c.reg addr) c.writes)
        (configBank pub c) (configBank pub c') := by
  refine ⟨{c with pc := next, reg := Function.update c.reg dst (WriteLog.memory c.writes (c.reg addr))}, rfl, ?_⟩
  exact loadPrivate_run dst addr pub c.persistent c.reg c.writes

/-- Uniform bound in the width and number of writes. No step loops over the
numeric value of the address. -/
theorem loadPrivate_cost_le (a : Word w) (log : WriteLog w) :
    17*w + 8 + AddressLog.loadCost a log ≤ (13*w+6)*log.length + 24*w + 15 := by
  have h := AddressLog.loadCost_le a log
  omega

end RAMTape.ISA

end VPVNP
end Computability
end OAI
