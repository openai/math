import OAI.Computability.VPVNP.RAMProcessorOrdinal

/-!
# Charged probe entry and post-emission timestamps

Startup and every external probe enter the same precharge. A successful
precharge preserves the saved call start and current ordinal. Emission can
therefore read them before the separate ordinal increment.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.CallCredit

open BurstRAM

variable {w : ℕ}

/-- Charge a probe against call, site and global credit, and increment the cumulative cost. An
exhausted allowance or cost overflow rejects before the probe is staged. -/
def prepareProbe : FiniteRoutine Port := Charges.routine Port.budget .charge

theorem prepareProbe_run (H fuelCap fuel call site : ℕ) (cap g c : Word w) (saved ord : List Bool)
    (hg : 0 < g.val) (hc : c.val + 1 < 2 ^ w) :
    prepareProbe.Runs (8*w+6) (bank H fuelCap fuel (call+1) (site+1) cap g c saved ord)
      (bank H fuelCap fuel call site cap (Charges.prevWord g) ⟨c.val+1,hc⟩ saved ord) := by
  let before := bank H fuelCap fuel (call+1) (site+1) cap g c saved ord
  have h := Charges.liftRun budget_injective before (entry := .charge) (exit := .done) (by decide)
    (Charges.chargeRun fuel call site g c hg hc)
  simp only [before, install_budget_bank, ↓reduceIte] at h
  exact h

/-- Failed precharging updates only budget ports and cannot reach a probe
callback. The controls are physically at the rejecting halt. -/
theorem prepareProbe_reject (H fuelCap fuel call site : ℕ) (cap g c : Word w) (saved ord : List Bool)
    (bad : call = 0 ∨ site = 0 ∨ g.val = 0 ∨ 2 ^ w ≤ c.val + 1) :
    let before := bank H fuelCap fuel call site cap g c saved ord
    ∃ raw, StackRuns prepareProbe.body.standalone (Charges.failureTicks call site g)
      (some .charge) before (some .reject) (installStacks Port.budget before raw) := by
  obtain ⟨raw, hr⟩ := Charges.chargeReject fuel call site g c bad
  let before := bank H fuelCap fuel call site cap g c saved ord
  have h := Charges.liftRun budget_injective before (entry := .charge) (exit := .reject)
    (by decide) hr
  simp only [before, install_budget_bank, show Charges.State.reject ≠ .done by decide, ↓reduceIte] at h
  exact ⟨_, h⟩

@[simp] theorem prepareProbe_halt :
    prepareProbe.body.standalone (some .reject) = .halt false := rfl

theorem finishProbe_bank {w : ℕ} (H fuelCap fuel call site : ℕ) (cap g c o : Word w)
    (saved : List Bool) (ho : o.val + 1 < 2 ^ w) :
    finishProbe.Runs (4*w+2) (bank H fuelCap fuel call site cap g c saved (wordBits o))
      (bank H fuelCap fuel call site cap g c saved (wordBits (⟨o.val+1,ho⟩ : Word w))) := by
  have he := finishProbe_run o ho (bank H fuelCap fuel call site cap g c saved (wordBits o)) rfl rfl
  convert he using 1
  funext p
  cases p <;> rfl

/-- Run the record callback after paying for the probe and before increasing
its ordinal. The callback may use the saved timestamp words and may update
the surrounding record buffers. -/
def withProbe {K : Type} (ports : Port → K) (emit : FiniteRoutine K) : FiniteRoutine K :=
  ((prepareProbe.onPorts ports).followedBy emit).followedBy (finishProbe.onPorts ports)

theorem withProbe_run {K : Type} [DecidableEq K] {ports : Port → K} (hp : Function.Injective ports)
    (emit : FiniteRoutine K) (before afterRecord : Stacks K) (H fuelCap fuel call site : ℕ)
    (cap g c o : Word w) (saved : List Bool) (hg : 0 < g.val) (hc : c.val+1 < 2^w)
    (ho : o.val+1 < 2^w) (emitTicks : ℕ)
    (hr : let charged := bank H fuelCap fuel call site cap (Charges.prevWord g) ⟨c.val+1,hc⟩ saved (wordBits o)
          emit.Runs emitTicks (installStacks ports before charged)
            (installStacks ports afterRecord charged)) :
    (withProbe ports emit).Runs (8*w+6 + emitTicks + (4*w+2))
      (installStacks ports before (bank H fuelCap fuel (call+1) (site+1) cap g c saved (wordBits o)))
      (installStacks ports afterRecord (bank H fuelCap fuel call site cap (Charges.prevWord g)
        ⟨c.val+1,hc⟩ saved (wordBits (⟨o.val+1,ho⟩ : Word w)))) := by
  have h₁ := prepareProbe.runs_onPorts hp before
    (prepareProbe_run H fuelCap fuel call site cap g c saved (wordBits o) hg hc)
  have h₂ := finishProbe.runs_onPorts hp afterRecord
    (finishProbe_bank H fuelCap fuel call site cap (Charges.prevWord g) ⟨c.val+1,hc⟩ o saved ho)
  exact (h₁.followedBy hr).followedBy h₂

end RAMTape.CallCredit

end VPVNP
end Computability
end OAI
