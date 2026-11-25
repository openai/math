import OAI.Computability.BorderVNP.TeamOpcodeDispatch
import OAI.Computability.BorderVNP.TeamTapeHandoffStartup
import OAI.Computability.VPVNP.SliceArithmeticCallClear
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-!
# Processor clock and architecture on a common stack bank

The word dispatcher uses the persistent architectural register bank. Its clock
guard has six separate registers. A private call copies its length from the
architectural bank, and a successful instruction records its first probe tick
on a separate stack. No architectural register is changed by this clock code.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamLocalClock

open VPVNP RAMTape BurstRAM RAMTape.PublicExprMachine TeamTapeHandoff

variable {w p r k m : ℕ}

/-- Work port layout of the callback loop. The private burst cap is a read-only parameter. -/
inductive Port (r k : ℕ) where
  | isa (port : ISA.Port r k)
  | meter (port : ISA.Port 6 0)
  | stamp | copyScratch | maxBurst
  deriving DecidableEq, Fintype

/-- Put the logged architectural bank and the six-word clock bank at disjoint physical ports. -/
def banks (pub : Fin k → Word w) (s : PrivateRAM.LogConfig w p r) (reg : Fin 6 → Word w)
    (maxBurst : Word w) (stamp : List Bool) : Stacks (Port r k)
  | .isa u => ISA.configBank pub s u
  | .meter u => ISA.bank Fin.elim0 0 reg [] u
  | .stamp => stamp
  | .copyScratch => []
  | .maxBurst => wordBits maxBurst

/-- Canonical instruction entry; no previous probe data or transient burst word is available. -/
def bank (pub : Fin k → Word w) (s : TeamOpcode.State w p r) (H left elapsed maxBurst : Word w) :
    Stacks (Port r k) := banks pub s.logged (chargeRegisters H left elapsed 0) maxBurst []

/-- Replace a word stack from a disjoint read-only source, preserving its bit order. -/
def assign (src dst : Port r k) : FiniteRoutine (Port r k) :=
  (SliceArithmetic.CallClear.clear dst).followedBy
    (SuccessorFields.prependCopy src dst Port.copyScratch)

/-- Copying the length register into the meter takes a linear number of bit instructions
and preserves the actual program state at a handoff. -/
theorem assign_runs (src dst : Port r k) (hd : src ≠ dst) (hs : src ≠ .copyScratch)
    (ht : dst ≠ .copyScratch) (s : Stacks (Port r k)) (hc : s .copyScratch = []) :
    (assign src dst).Runs ((s dst).length+1+(5*(s src).length+2)) s (Function.update s dst (s src)) := by
  have clear := SliceArithmetic.CallClear.clear_runs dst s
  have copy := SuccessorFields.prependCopy_runs src dst Port.copyScratch hd hs ht
    (Function.update s dst []) (by simp [Function.update_of_ne ht.symm, hc])
  simp only [Function.update_of_ne hd, Function.update_self, List.append_nil, Function.update_idem] at copy
  exact clear.followedBy copy

/-- The chosen private-call length is the current word in the named register. -/
def stageLength (length : Fin r) : FiniteRoutine (Port r k) := assign (.isa (.reg length)) (.meter (.reg 3))

private theorem banks_update (pub : Fin k → Word w) (s : PrivateRAM.LogConfig w p r)
    (reg : Fin 6 → Word w) (max : Word w) (stamp : List Bool) (dst : Fin 6) (x : Word w) :
    Function.update (banks pub s reg max stamp) (.meter (.reg dst)) (wordBits x) =
      banks pub s (Function.update reg dst x) max stamp := by
  funext u
  cases u with
  | meter v =>
    cases v with
    | reg j => by_cases h : j = dst <;> simp [banks, ISA.bank, h]
    | pub j => exact Fin.elim0 j
    | persistent | work | logPort => simp [banks, ISA.bank]
  | isa | stamp | copyScratch | maxBurst => simp [banks]

/-- Physical staging from an existing RAM register, including when its word is zero. -/
theorem stageLength_runs (pub : Fin k → Word w) (s : TeamOpcode.State w p r)
    (H left elapsed max : Word w) (j : Fin r) :
    (stageLength (k := k) j).Runs (6*w+3) (bank pub s H left elapsed max)
      (banks pub s.logged (chargeRegisters H left elapsed (s.reg j)) max []) := by
  have h := assign_runs (Port.isa (.reg j)) (.meter (.reg 3)) (by simp) (by simp) (by simp)
    (bank pub s H left elapsed max) rfl
  have he : Function.update (chargeRegisters H left elapsed 0) 3 (s.reg j) =
      chargeRegisters H left elapsed (s.reg j) := by funext a; fin_cases a <;> rfl
  change (stageLength j).Runs ((wordBits (0 : Word w)).length+1+(5*(wordBits (s.reg j)).length+2))
    _ (Function.update (banks pub s.logged (chargeRegisters H left elapsed 0) max [])
      (.meter (.reg 3)) (wordBits (s.reg j))) at h
  rwa [length_wordBits, length_wordBits, show w+1+(5*w+2)=6*w+3 by omega, banks_update, he] at h

/-- Replace only the meter bank after a word-kernel operation. -/
theorem install_meter (pub : Fin k → Word w) (s : PrivateRAM.LogConfig w p r) (reg reg' : Fin 6 → Word w)
    (max : Word w) (stamp : List Bool) :
    installStacks Port.meter (banks pub s reg max stamp) (ISA.bank Fin.elim0 0 reg' []) =
      banks pub s reg' max stamp := by
  funext u
  cases u with
  | meter v => exact installStacks_at (fun _ _ h => Port.meter.inj h) _ _ _
  | isa | stamp | copyScratch | maxBurst => rw [installStacks_outside (hl := fun _ => by simp)]; rfl

/-- Replace only the architecture bank after dispatching an opcode. -/
theorem install_isa (pub : Fin k → Word w) (s s' : PrivateRAM.LogConfig w p r)
    (reg : Fin 6 → Word w) (max : Word w) (stamp : List Bool) :
    installStacks Port.isa (banks pub s reg max stamp) (ISA.configBank pub s') =
      banks pub s' reg max stamp := by
  funext u
  cases u with
  | isa v => exact installStacks_at (fun _ _ h => Port.isa.inj h) _ _ _
  | meter | stamp | copyScratch | maxBurst => rw [installStacks_outside (hl := fun _ => by simp)]; rfl

/-- Install a meter operation without disturbing any saved probe or architectural operand. -/
theorem meter_runs {a : FiniteRoutine (ISA.Port 6 0)} {t : ℕ} (pub : Fin k → Word w)
    (s : PrivateRAM.LogConfig w p r) (reg reg' : Fin 6 → Word w) (max : Word w) (stamp : List Bool)
    (h : a.Runs t (ISA.bank Fin.elim0 0 reg []) (ISA.bank Fin.elim0 0 reg' [])) :
    (a.onPorts Port.meter).Runs t (banks pub s reg max stamp) (banks pub s reg' max stamp) := by
  simpa only [install_meter] using a.runs_onPorts (fun _ _ h => Port.meter.inj h) (banks pub s reg max stamp) h

/-- Clear the staged burst and arithmetic result words to the canonical zero word. -/
def clearMeter : FiniteRoutine (Port r k) :=
  ((ISA.loadLiteral 0 (3 : Fin 6)).followedBy (ISA.loadLiteral 0 (5 : Fin 6))).onPorts Port.meter

/-- Clearing the staging registers restores the entry invariant while preserving the stamp. -/
theorem clearMeter_runs (pub : Fin k → Word w) (s : PrivateRAM.LogConfig w p r)
    (H left elapsed q scratch max : Word w) (stamp : List Bool) :
    clearMeter.Runs (2*(8*w+3)) (banks pub s ![H,left,elapsed,q,1,scratch] max stamp)
      (banks pub s (chargeRegisters H left elapsed 0) max stamp) := by
  let reg := ![H,left,elapsed,q,(1 : Word w),scratch]
  let r' := Function.update reg (3 : Fin 6) (0 : Word w)
  have first := ISA.loadLiteral_run 0 3 Fin.elim0 (0 : Word w) reg []
  have second := ISA.loadLiteral_run 0 5 Fin.elim0 (0 : Word w) r' []
  have he : Function.update r' 5 (Fin.ofNat (2^w) 0) = chargeRegisters H left elapsed 0 := by
    funext j; fin_cases j <;> rfl
  rw [he] at second
  exact meter_runs pub s reg _ max stamp (by simpa only [two_mul] using first.followedBy second)

/-- After a successful charge, subtract the private burst length from the new elapsed
tick. This recovers the first probe time, one past the previous logical tick. -/
def finishCharge : FiniteRoutine (Port r k) :=
  (((Arithmetic.sub.code 5 2 3).onPorts Port.meter).followedBy
    (SuccessorFields.prependCopy (.meter (.reg 5)) Port.stamp Port.copyScratch)).followedBy clearMeter

/-- The first probe timestamp is saved separately, even when the private call reads zero
words. Transient meter words are cleared before the callback takes control. -/
theorem finishCharge_runs (pub : Fin k → Word w) (s : PrivateRAM.LogConfig w p r)
    (H left elapsed q max : Word w) (pass : decision H.val left.val q.val = .execute)
    (safe : elapsed.val+left.val < 2^w) :
    ∃ T ≤ 150*(w+1)^2 + 5*w+2 + 2*(8*w+3), finishCharge.Runs T
      (banks pub s (chargedRegisters H left elapsed q) max [])
      (banks pub s (chargeRegisters (packed w (H.val-(1+q.val))) (packed w (left.val-(1+q.val)))
        (packed w (elapsed.val+(1+q.val))) 0) max (wordBits (packed w (elapsed.val+1)))) := by
  let reg := chargedRegisters H left elapsed q
  let firstTick := packed w (elapsed.val+1)
  let r' := Function.update reg (5 : Fin 6) firstTick
  obtain ⟨t, ht, hr⟩ := Arithmetic.runs Arithmetic.sub (5 : Fin 6) 2 3 Fin.elim0 (0 : Word w) reg []
  obtain ⟨_, _, htime⟩ := charge_values H left elapsed q pass safe
  have hv : Arithmetic.sub.eval (reg 2).val (reg 3).val = elapsed.val+1 := by
    change (packed w (elapsed.val+(1+q.val))).val - q.val = elapsed.val+1
    rw [htime]; omega
  rw [hv] at hr
  have first := meter_runs pub s reg r' max [] hr
  let b := banks pub s r' max []
  have second := SuccessorFields.prependCopy_runs (Port.meter (.reg 5)) Port.stamp Port.copyScratch
    (by simp) (by simp) (by simp) b rfl
  have hst : Function.update b Port.stamp (wordBits firstTick ++ []) =
      banks pub s r' max (wordBits firstTick) := by
    funext u; cases u <;> simp [banks, b]
  change (SuccessorFields.prependCopy (.meter (.reg 5)) Port.stamp Port.copyScratch).Runs
    (5*(wordBits firstTick).length+2) b (Function.update b Port.stamp (wordBits firstTick ++ [])) at second
  rw [hst, length_wordBits] at second
  let h' := packed w (H.val-(1+q.val))
  let g' := packed w (left.val-(1+q.val))
  let e' := packed w (elapsed.val+(1+q.val))
  have he : r' = ![h',g',e',q,(1 : Word w),firstTick] := by funext j; fin_cases j <;> rfl
  have last := clearMeter_runs pub s h' g' e' q firstTick max (wordBits firstTick)
  rw [← he] at last
  exact ⟨t+(5*w+2)+2*(8*w+3), by omega, (first.followedBy second).followedBy last⟩

end TeamLocalClock

end BorderVNP
end Computability
end OAI
