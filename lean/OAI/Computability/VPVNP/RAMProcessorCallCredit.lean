import OAI.Computability.VPVNP.RAMProcessorCreditReset
import OAI.Computability.VPVNP.RAMProcessorProbeCredit
import OAI.Computability.VPVNP.RAMProcessorGlobalCredit

/-!
# Starting a metered call

Before any instruction dispatch, restore the two unary credits from their
public tallies, save the current cost as the call start, reset the probe
ordinal to zero, and take the mandatory startup charge. A call can therefore
start with one remaining unit and complete without a probe.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.CallCredit

open BurstRAM

variable {w : ℕ}

/-- Startup first prepares the per-call state, then charges its unit. -/
def startCall : FiniteRoutine Port := resetCredits.followedBy prepareProbe

/-- Stack-step count for restoring call and instruction credits, saving the start cost and
resetting the probe ordinal, accounting for the lengths of their previous contents. -/
def resetTicks (w H fuelCap fuel call : ℕ) (saved ord : List Bool) : ℕ :=
  call + fuel + saved.length + ord.length + 7*(H + fuelCap + 2*w) + 12

theorem startCall_run (H fuelCap fuel call site : ℕ) (cap g c : Word w) (saved ord : List Bool)
    (hH : 0 < H) (hs : 0 < site) (hg : 0 < g.val) (hc : c.val + 1 < 2 ^ w) :
    startCall.Runs (resetTicks w H fuelCap fuel call saved ord + (8*w+6))
      (bank H fuelCap fuel call site cap g c saved ord)
      (bank H fuelCap fuelCap (H-1) (site-1) cap (Charges.prevWord g) ⟨c.val+1,hc⟩
        (wordBits c) (wordBits (0 : Word w))) := by
  cases H with
  | zero => contradiction
  | succ a =>
    cases site with
    | zero => contradiction
    | succ s =>
      exact (resetCredits_run (a+1) fuelCap fuel call (s+1) cap g c saved ord).followedBy
        (prepareProbe_run (a+1) fuelCap fuelCap a s cap g c (wordBits c) (wordBits (0 : Word w)) hg hc)

/-- In a sequenced routine a rejecting state of the second stage remains a
rejecting state, with no transition past the failure. -/
private theorem followRight {K : Type} [DecidableEq K] {a b : FiniteRoutine K}
    {n : ℕ} {s t : Stacks K} {exit : b.State}
    (h : StackRuns b.body.standalone n (some b.body.entry) s (some exit) t) :
    StackRuns (a.followedBy b).body.standalone n (some (.inr b.body.entry)) s
      (some (.inr exit)) t := by
  let labels (q : Option b.State) : Option (a.State ⊕ b.State) := q.elim none (some ∘ Sum.inr)
  have hc (q : Option b.State) (hn : (b.body.standalone q).returns = false) :
      (a.followedBy b).body.standalone (labels q) = (b.body.standalone q).rename id labels := by
    cases q with
    | none => contradiction
    | some x => rfl
  have h' := h.lift id Function.injective_id labels s hc
  have he (u : Stacks K) : installStacks id s u = u := by
    funext i; exact installStacks_at Function.injective_id s u i
  rw [he, he] at h'
  exact h'

theorem startCall_reject (H fuelCap fuel call site : ℕ) (cap g c : Word w) (saved ord : List Bool)
    (bad : H = 0 ∨ site = 0 ∨ g.val = 0 ∨ 2 ^ w ≤ c.val + 1) :
    ∃ out, StackRuns startCall.body.standalone
      (resetTicks w H fuelCap fuel call saved ord + Charges.failureTicks H site g)
      (some startCall.body.entry) (bank H fuelCap fuel call site cap g c saved ord)
      (some (.inr .reject)) out := by
  have hreset := resetCredits_run H fuelCap fuel call site cap g c saved ord
  have hr := hreset.link startCall.body Sum.inl (some (.inr prepareProbe.body.entry)) (fun _ => rfl)
  obtain ⟨_, hbad⟩ := prepareProbe_reject H fuelCap fuelCap H site cap g c
    (wordBits c) (wordBits (0 : Word w)) bad
  exact ⟨_, hr.trans (followRight (a := resetCredits) (b := prepareProbe) hbad)⟩

@[simp] theorem startCall_halt : startCall.body.standalone (some (.inr .reject)) = .halt false := rfl

/-- Initialize the binary allowance from the supplied cap and incoming cost
before starting the site's first live call. -/
def firstCall : FiniteRoutine Port := GlobalCredit.routine.followedBy startCall

theorem firstCall_run (H fuelCap fuel call site : ℕ) (cap old c : Word w) (saved ord : List Bool)
    (hH : 0 < H) (hs : 0 < site) (hlt : c.val < cap.val) :
    let hc : c.val + 1 < 2 ^ w := (Nat.succ_le_of_lt hlt).trans_lt cap.isLt
    firstCall.Runs ((16*w+7) + (resetTicks w H fuelCap fuel call saved ord + (8*w+6)))
      (bank H fuelCap fuel call site cap old c saved ord)
      (bank H fuelCap fuelCap (H-1) (site-1) cap (Charges.prevWord (cap-c)) ⟨c.val+1,hc⟩
        (wordBits c) (wordBits (0 : Word w))) := by
  have hinit := GlobalCredit.bank_run H fuelCap fuel call site cap old c saved ord hlt.le
  have hg : 0 < (cap-c).val := by rw [GlobalCredit.remaining_val cap c hlt.le]; omega
  exact hinit.followedBy
    (startCall_run H fuelCap fuel call site cap (cap-c) c saved ord hH hs hg
      ((Nat.succ_le_of_lt hlt).trans_lt cap.isLt))

/-- After a permitted charge, the two binary counters continue to sum to
the cap, and the incremented cost fits the same word. -/
theorem remaining_after_charge {cap g c : Word w} (hg : 0 < g.val)
    (hcap : g.val + c.val = cap.val) :
    (Charges.prevWord g).val + (c.val + 1) = cap.val ∧ c.val + 1 < 2 ^ w := by
  have := cap.isLt
  change g.val - 1 + (c.val + 1) = cap.val ∧ _
  omega

/-- A probe ordinal counts only the probes since startup. Its next value
therefore fits even if the probe takes the global cost exactly to the cap. -/
theorem ordinal_fits {saved o c : Word w} (hstart : saved.val + (1 + o.val) = c.val) :
    o.val + 1 < 2 ^ w := by have := c.isLt; omega

end RAMTape.CallCredit

end VPVNP
end Computability
end OAI
