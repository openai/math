import OAI.Computability.VPVNP.RAMProcessorCreditPorts
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord
import OAI.Computability.VPVNP.RAMTapeWordSimple

/-!
# Initializing the processor's remaining global allowance

The input cap and incoming cumulative cost occupy binary words. The processor
copies both words, subtracts the cost from the cap, and rejects on a final
borrow. The cap, the cumulative cost, and the other call counters survive this
operation. The running time is linear in the word width and the old output.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.CallCredit.GlobalCredit

open BurstRAM TapeWord SuccessorFields

private def stages : FiniteRoutine Port :=
  (prependCopy Port.globalCap .arithA .copyA).followedBy
    (prependCopy (.budget .cost) .arithB .copyA)

/-- Control states for staging the cap and cost, clearing the destination and subtracting to
compute the remaining global credit. -/
inductive State where
  | stage (q : stages.State)
  | clear
  | subtract (q : ScanState)
  deriving Fintype

private def ports : ScanPort → Port
  | .left => .arithA
  | .right => .arithB
  | .tmp => .budget .tmp
  | .out => .budget .globalLeft

private def resume : ScanState → Option State
  | .done false => none
  | q => some (.subtract q)

/-- The no-borrow exit returns to the caller. A borrow stops the entire path. -/
def body : Routine Port State where
  entry := State.stage stages.body.entry
  code := fun
    | .stage q => stages.body.install State.stage (some .clear) q
    | .clear => .pop (.budget .globalLeft) fun b => b.elim (some (.subtract (.left false))) (fun _ => some .clear)
    | .subtract (.done _) => .halt false
    | .subtract q => (scanCode subBit q).rename ports resume

/-- Compute the remaining global credit by subtracting cumulative cost from the cap, rejecting
if subtraction borrows past the word. -/
abbrev routine : FiniteRoutine Port := ⟨State, body⟩

@[simp] theorem borrow_halts : routine.body.code (.subtract (.done true)) = .halt false := rfl

private def staged (s : Stacks Port) (a b : List Bool) : Stacks Port :=
  Function.update (Function.update s .arithA a) .arithB b

private theorem stageRun {w : ℕ} (s : Stacks Port) (cap cost : Word w)
    (hcap : s .globalCap = wordBits cap) (hcost : s (.budget .cost) = wordBits cost)
    (hcopy : s .copyA = []) (ha : s .arithA = []) (hb : s .arithB = []) :
    stages.Runs (10*w+4) s (staged s (wordBits cap) (wordBits cost)) := by
  have h₁ := prependCopy_runs Port.globalCap .arithA .copyA (by decide) (by decide) (by decide) s hcopy
  simp only [hcap, ha, List.append_nil, length_wordBits] at h₁
  let s' := Function.update s .arithA (wordBits cap)
  have h₂ := prependCopy_runs (Port.budget .cost) .arithB .copyA (by decide) (by decide) (by decide) s'
    (by simpa [s'] using hcopy)
  have hc' : s' (.budget .cost) = wordBits cost := by simpa [s'] using hcost
  have hb' : s' .arithB = [] := by simpa [s'] using hb
  simp only [hc', hb', List.append_nil, length_wordBits] at h₂
  rw [show 10*w+4 = (5*w+2)+(5*w+2) by omega]
  exact h₁.followedBy h₂

private theorem clearRun (s : Stacks Port) (xs : List Bool) :
    StackRuns routine.body.standalone (xs.length+1) (some .clear)
      (Function.update s (.budget .globalLeft) xs) (some (.subtract (.left false)))
      (Function.update s (.budget .globalLeft) []) := by
  induction xs with
  | nil =>
    refine .cons (.pop rfl) ?_
    simp only [Function.update_self, List.head?_nil, List.tail_nil, Option.elim_none, Function.update_idem]
    exact .nil ..
  | cons b xs ih =>
    refine .cons (.pop rfl) ?_
    simp only [Function.update_self, List.head?_cons, List.tail_cons, Option.elim_some, Function.update_idem]
    exact ih

private theorem subtractRun {w : ℕ} (s : Stacks Port) (cap cost : Word w)
    (ha : s .arithA = []) (hb : s .arithB = []) (ht : s (.budget .tmp) = []) :
    StackRuns routine.body.standalone (5*w+2) (some (.subtract (.left false)))
      (Function.update (staged s (wordBits cap) (wordBits cost)) (.budget .globalLeft) [])
      (resume (.done (decide (cap.val < cost.val))))
      (Function.update s (.budget .globalLeft) (wordBits (cap-cost))) := by
  have hp : Function.Injective ports := by decide
  have rows (q : ScanState) (hn : (scanCode subBit q).returns = false) :
      routine.body.standalone (resume q) = (scanCode subBit q).rename ports resume := by
    cases q <;> first | rfl | contradiction
  have hr := (ScanOp.word_run .sub cap cost).lift ports hp resume s rows
  have hf : (scan subBit false (wordBits cap) (wordBits cost)).2 = decide (cap.val < cost.val) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [value_wordBits, Bool.toNat_false, Nat.add_zero, decide_eq_true_eq] using
      subScan_borrow (c := false) (x := wordBits cap) (y := wordBits cost) (by simp)
  change StackRuns _ _ _ (installStacks ports s (scanStacks (wordBits cap) (wordBits cost) [] []))
    (resume (.done (scan subBit false (wordBits cap) (wordBits cost)).2))
    (installStacks ports s (scanStacks [] [] [] (wordBits (cap-cost)))) at hr
  rw [hf] at hr
  have hi : installStacks ports s (scanStacks (wordBits cap) (wordBits cost) [] []) =
      Function.update (staged s (wordBits cap) (wordBits cost)) (.budget .globalLeft) [] := by
    apply installStacks_frame hp
    · intro p; cases p <;> simp [staged, ports, scanStacks, ht]
    · intro i hout
      have hl : i ≠ .arithA := (hout .left).symm
      have hr : i ≠ .arithB := (hout .right).symm
      have ho : i ≠ .budget .globalLeft := (hout .out).symm
      simp [staged, Function.update_of_ne, hl, hr, ho]
  have ho : installStacks ports s (scanStacks [] [] [] (wordBits (cap-cost))) =
      Function.update s (.budget .globalLeft) (wordBits (cap-cost)) := by
    apply installStacks_frame hp
    · intro p; cases p <;> simp [ports, scanStacks, ha, hb, ht]
    · intro i hout; exact Function.update_of_ne (Ne.symm (hout .out)) ..
  rwa [hi, ho] at hr

/-- Every valid pair of input words has a deterministic path of the same
length. The final control is the rejecting halt exactly when the cost
exceeds the cap. All ports except the global allowance are restored. -/
theorem run {w : ℕ} (s : Stacks Port) (cap cost : Word w)
    (hcap : s .globalCap = wordBits cap) (hcost : s (.budget .cost) = wordBits cost)
    (hcopy : s .copyA = []) (ha : s .arithA = []) (hb : s .arithB = []) (ht : s (.budget .tmp) = []) :
    StackRuns routine.body.standalone ((s (.budget .globalLeft)).length + 15*w+7)
      (some routine.body.entry) s (if cap.val < cost.val then some (.subtract (.done true)) else none)
      (Function.update s (.budget .globalLeft) (wordBits (cap-cost))) := by
  let t := staged s (wordBits cap) (wordBits cost)
  have hs := (stageRun s cap cost hcap hcost hcopy ha hb).link routine.body State.stage
    (some .clear) (fun _ => rfl)
  have hc := clearRun t (t (.budget .globalLeft))
  rw [Function.update_eq_self] at hc
  have he : t (.budget .globalLeft) = s (.budget .globalLeft) := by simp [t, staged]
  rw [he] at hc
  have hu := subtractRun s cap cost ha hb ht
  rw [show (s (.budget .globalLeft)).length+15*w+7 =
    (10*w+4)+((s (.budget .globalLeft)).length+1)+(5*w+2) by omega]
  have hall := (hs.trans hc).trans hu
  rw [show (if cap.val < cost.val then some (State.subtract (.done true)) else none) =
    resume (.done (decide (cap.val < cost.val))) by by_cases h : cap.val < cost.val <;> simp [h, resume]]
  exact hall

/-- The arithmetic word represents ordinary natural subtraction whenever
initialization returns, including at exact exhaustion of the global allowance. -/
theorem remaining_val {w : ℕ} (cap cost : Word w) (hle : cost.val ≤ cap.val) :
    (cap-cost).val = cap.val - cost.val := by
  rw [Fin.val_sub]
  have hcap := cap.isLt
  have hcost := cost.isLt
  rw [show 2^w - cost.val + cap.val = (cap.val-cost.val) + 2^w by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

private theorem update_bank {w : ℕ} (H fuelCap fuel call site : ℕ) (cap old cost out : Word w)
    (saved ord : List Bool) :
    Function.update (bank H fuelCap fuel call site cap old cost saved ord) (.budget .globalLeft) (wordBits out) =
      bank H fuelCap fuel call site cap out cost saved ord := by
  funext p
  cases p with
  | budget p => cases p <;> rfl
  | _ => rfl

theorem bank_run {w : ℕ} (H fuelCap fuel call site : ℕ) (cap old cost : Word w) (saved ord : List Bool)
    (hle : cost.val ≤ cap.val) :
    routine.Runs (16*w+7) (bank H fuelCap fuel call site cap old cost saved ord)
      (bank H fuelCap fuel call site cap (cap-cost) cost saved ord) := by
  have hr := run (bank H fuelCap fuel call site cap old cost saved ord) cap cost rfl rfl rfl rfl rfl rfl
  rw [ite_eq_right (Nat.not_lt.mpr hle), update_bank] at hr
  change StackRuns _ ((wordBits old).length+15*w+7) _ _ none _ at hr
  rw [length_wordBits, show w+15*w+7 = 16*w+7 by omega] at hr
  exact hr

theorem bank_reject {w : ℕ} (H fuelCap fuel call site : ℕ) (cap old cost : Word w) (saved ord : List Bool)
    (hbad : cap.val < cost.val) :
    StackRuns routine.body.standalone (16*w+7) (some routine.body.entry)
      (bank H fuelCap fuel call site cap old cost saved ord) (some (.subtract (.done true)))
      (bank H fuelCap fuel call site cap (cap-cost) cost saved ord) := by
  have hr := run (bank H fuelCap fuel call site cap old cost saved ord) cap cost rfl rfl rfl rfl rfl rfl
  rw [ite_eq_left hbad, update_bank] at hr
  change StackRuns _ ((wordBits old).length+15*w+7) _ _ _ _ at hr
  rw [length_wordBits, show w+15*w+7 = 16*w+7 by omega] at hr
  exact hr

end RAMTape.CallCredit.GlobalCredit

end VPVNP
end Computability
end OAI
