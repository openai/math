import OAI.Computability.VPVNP.CompressorSlicePrefix
import OAI.Computability.VPVNP.PrimedScheduleRAM

/-!
# Preparing the interval-scan workspace

The workspace consists, in order, of two totals, two incidence-count arrays
and two field-start arrays. A single clearing sweep initializes both totals
and both count arrays. Two prefix sweeps then produce the starts from the
original external width arrays. The pair records begin immediately after this
workspace.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SliceRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- Clear the cell at the public base plus the persistent index, then advance. -/
def clearOps : List (Op 4 1) :=
  [.stateWord 0, .publicWord 1 0, .binary .add 1 1 0, .constant 2 0,
    .write 1 2, .constant 3 1, .binary .add 0 0 3]

/-- Native report for zeroing one workspace cell and advancing the clearing cursor. -/
def clearReport (base i : Word w) : Report w :=
  ⟨[.tick, .tick, .tick, .tick, .write (base + i) 0, .tick, .tick], some (i + 1)⟩

theorem clearVisit_native (base i : Word w) (mem : Memory w) :
    let M := (template clearOps 0).instantiate w (fun _ => base)
    execute M.program 8 (M.program.start i) mem [] = some (clearReport base i) := by
  let M := (template clearOps 0).instantiate w (fun _ => base)
  change execute M.program (1 + clearOps.length) ⟨M.entry,i,fun _ => 0,fun _ => 0⟩ mem [] = _
  rw [execute_template, run_eq_trace]
  simp (config := { decide := true }) [clearOps, trace, Op.effect, BinaryOp.eval,
    Function.update, clearReport]
  rfl

/-- The clearing segment starts from arbitrary memory and writes each visited
cell once. All addresses outside its interval retain their original contents. -/
theorem clearPass_run (base : Word w) (n : ℕ) (hfit : base.val + n ≤ 2^w)
    (hlen : n < 2^w) (mem : Memory w) :
    let M := (template clearOps 0).instantiate w (fun _ => base)
    ∃ rs, runSegment M.program 8 (some 0) mem (List.replicate n []) = some rs ∧
      (∀ x, base.val ≤ x → x < base.val + n → after mem (eventLog rs) x = 0) ∧
      (∀ x, (x < base.val ∨ base.val + n ≤ x) → after mem (eventLog rs) x = mem x) ∧
      endState (some 0) rs = some (Fin.ofNat (2^w) n) ∧ rs.length = n ∧
      ∀ r ∈ rs, r.probes = 1 ∧ r.events.length + 1 = 8 := by
  let M := (template clearOps 0).instantiate w (fun _ => base)
  induction n with
  | zero => exact ⟨[], rfl, fun _ _ _ => by omega, fun _ _ => rfl, rfl, rfl, by simp⟩
  | succ n ih =>
    let i := Fin.ofNat (2^w) n
    have hi : i.val = n := Nat.mod_eq_of_lt (by omega)
    have ha : (base + i).val = base.val + n := by
      rw [Fin.val_add, hi, Nat.mod_eq_of_lt (by omega)]
    have he : i + 1 = Fin.ofNat (2^w) (n+1) := by
      apply Fin.ext
      rw [Fin.val_add, hi, Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2^w by omega)]
      rfl
    obtain ⟨rs,hr,hzero,hout,hend,hℓ,hcost⟩ := ih (by omega) (by omega)
    let r := clearReport base i
    have hm : after mem (eventLog (rs ++ [r])) =
        writeMemory (after mem (eventLog rs)) (base + i) 0 := by
      simp only [eventLog, List.flatMap_append, after, List.foldl_append]
      rfl
    refine ⟨rs ++ [r], ?_, ?_, ?_, ?_, by simp [hℓ], ?_⟩
    · rw [List.replicate_succ', PrimedSchedule.runSegment_append, hr]
      simp only [Option.bind_some, hend, runSegment, clearVisit_native, Option.map_some]
      rfl
    · intro x h₁ h₂
      rw [hm]
      by_cases hx : x = base.val + n
      · simp [writeMemory, ha, hx]
      · simpa [writeMemory, ha, hx] using hzero x h₁ (by omega)
    · intro x hx
      rw [hm]
      simpa [writeMemory, ha, show x ≠ base.val + n by omega] using hout x (by omega)
    · rw [endState_append]
      change some (i + 1) = _
      rw [he]
    · intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact hcost _ h
      · obtain rfl := List.mem_singleton.mp h
        exact ⟨rfl,rfl⟩

/-- Public input widths can be supplied in any two arrays disjoint from the
workspace. Their bounds and the first pair-record address fit the word size. -/
structure PreparationRegions (oldBase newBase B : Word w) (m n : ℕ) : Prop where
  oldWidthsFit : oldBase.val + m ≤ 2^w
  newWidthsFit : newBase.val + n ≤ 2^w
  frameBaseFits : B.val + 2 + 2*m + 2*n < 2^w
  oldApart : oldBase.val + m ≤ B.val ∨ B.val + 2 + 2*m + 2*n ≤ oldBase.val
  newApart : newBase.val + n ≤ B.val ∨ B.val + 2 + 2*m + 2*n ≤ newBase.val

/-- Start and total cells of the source fields. -/
def oldPrefixData (oldBase B : Word w) (m n : ℕ) : Fin 3 → Word w :=
  ![oldBase, Fin.ofNat _ (B.val + 2 + m + n), B]

/-- Start and total cells of the target fields. -/
def newPrefixData (newBase B : Word w) (m n : ℕ) : Fin 3 → Word w :=
  ![newBase, Fin.ofNat _ (B.val + 2 + 2*m + n), Fin.ofNat _ (B.val + 1)]

/-- Exact contents and footprint of the initialized workspace. -/
structure Prepared (oldBase newBase B : Word w) (old new : List ℕ) (initial mem : Memory w) : Prop where
  oldWidths : ∀ i (hi : i < old.length), (mem (oldBase.val + i)).val = old[i]
  newWidths : ∀ j (hj : j < new.length), (mem (newBase.val + j)).val = new[j]
  oldStarts : ∀ i, i < old.length → (mem (B.val + 2 + old.length + new.length + i)).val =
    (old.take i).sum
  newStarts : ∀ j, j < new.length → (mem (B.val + 2 + 2*old.length + new.length + j)).val =
    (new.take j).sum
  oldCounts : ∀ i, i < old.length → mem (B.val + 2 + i) = 0
  newCounts : ∀ j, j < new.length → mem (B.val + 2 + old.length + j) = 0
  oldTotal : (mem B.val).val = old.sum
  newTotal : (mem (B.val + 1)).val = new.sum
  outside : ∀ x, (x < B.val ∨ B.val + 2 + 2*old.length + 2*new.length ≤ x) → mem x = initial x

/-- Compose the physical memory effects of the three native segments. -/
def preparationAfter (mem : Memory w) (clear oldRun newRun : List (Report w)) : Memory w :=
  after (after (after mem (eventLog clear)) (eventLog oldRun)) (eventLog newRun)

/-- The three actual segments with their exact transfer of memory and
instruction and probe totals. The persistent word starts at zero in each segment. -/
structure PreparationRuns (oldBase newBase B : Word w) (m n : ℕ) (mem : Memory w)
    (clear oldRun newRun : List (Report w)) : Prop where
  clearNative : runSegment ((template clearOps 0).instantiate w (fun _ => B)).program 8
    (some 0) mem (List.replicate (2+m+n) []) = some clear
  oldNative : runSegment ((template prefixOps 0).instantiate w (oldPrefixData oldBase B m n)).program
    14 (some 0) (after mem (eventLog clear)) (List.replicate m []) = some oldRun
  newNative : runSegment ((template prefixOps 0).instantiate w (newPrefixData newBase B m n)).program
    14 (some 0) (after (after mem (eventLog clear)) (eventLog oldRun))
    (List.replicate n []) = some newRun
  clearLength : clear.length = 2+m+n
  oldLength : oldRun.length = m
  newLength : newRun.length = n
  probes : ((clear ++ oldRun ++ newRun).map Report.probes).sum = 2 + 5*(m+n)
  instructions : ((clear ++ oldRun ++ newRun).map (fun r => r.events.length + 1)).sum =
    16 + 22*(m+n)

private theorem sum_constant_cost {α : Type*} (f : α → ℕ) (rs : List α) (v : ℕ)
    (h : ∀ r ∈ rs, f r = v) : (rs.map f).sum = v * rs.length := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    rw [List.map_cons, List.sum_cons, h r (by simp), ih (fun t ht => h t (by simp [ht])),
      List.length_cons, Nat.mul_succ, Nat.add_comm]

/-- From the original width arrays and arbitrary workspace contents, produce
both indexed start arrays and zero counts for all source and target fields. -/
theorem preparation_run {oldBase newBase B : Word w} {old new : List ℕ}
    (regions : PreparationRegions oldBase newBase B old.length new.length)
    (hOldSum : old.sum < 2^w) (hNewSum : new.sum < 2^w) {mem : Memory w}
    (hOldWidths : ∀ i (hi : i < old.length), (mem (oldBase.val + i)).val = old[i])
    (hNewWidths : ∀ j (hj : j < new.length), (mem (newBase.val + j)).val = new[j]) :
    ∃ clear oldRun newRun,
      PreparationRuns oldBase newBase B old.length new.length mem clear oldRun newRun ∧
      Prepared oldBase newBase B old new mem (preparationAfter mem clear oldRun newRun) := by
  let O := oldPrefixData oldBase B old.length new.length
  let N := newPrefixData newBase B old.length new.length
  have hfit := regions.frameBaseFits
  have hoa := regions.oldApart
  have hna := regions.newApart
  have ho₀ : (O 0).val = oldBase.val := rfl
  have ho₁ : (O 1).val = B.val + 2 + old.length + new.length := Nat.mod_eq_of_lt (by omega)
  have ho₂ : (O 2).val = B.val := rfl
  have hn₀ : (N 0).val = newBase.val := rfl
  have hn₁ : (N 1).val = B.val + 2 + 2*old.length + new.length := Nat.mod_eq_of_lt (by omega)
  have hn₂ : (N 2).val = B.val + 1 := Nat.mod_eq_of_lt (by omega)
  have hoReg : PrefixRegions O old.length :=
    ⟨regions.oldWidthsFit, by omega, by omega, by omega, by omega⟩
  have hnReg : PrefixRegions N new.length :=
    ⟨regions.newWidthsFit, by omega, by omega, by omega, by omega⟩
  obtain ⟨clear,hcRun,hcZero,hcOutside,_,hcLen,hcCost⟩ :=
    clearPass_run B (2 + old.length + new.length) (by omega) (by omega) mem
  let cleared := after mem (eventLog clear)
  have hoW (i : ℕ) (hi : i < old.length) : (cleared ((O 0).val + i)).val = old[i] := by
    change (after mem (eventLog clear) (oldBase.val + i)).val = _
    rw [hcOutside _ (by omega)]
    exact hOldWidths i hi
  have hoZ : (cleared (O 2).val).val = 0 := by
    change (after mem (eventLog clear) B.val).val = 0
    rw [hcZero _ le_rfl (by omega)]
    rfl
  obtain ⟨oldRun,hoRun,ho,_,hoLen,hoCost⟩ :=
    prefixPass_run hoReg (by omega) hOldSum hoW hoZ
  let oldDone := after cleared (eventLog oldRun)
  have hnW (j : ℕ) (hj : j < new.length) : (oldDone ((N 0).val + j)).val = new[j] := by
    change (after cleared (eventLog oldRun) (newBase.val + j)).val = _
    rw [ho.outside _ (by omega) (by omega)]
    change (after mem (eventLog clear) (newBase.val + j)).val = _
    rw [hcOutside _ (by omega)]
    exact hNewWidths j hj
  have hnZ : (oldDone (N 2).val).val = 0 := by
    change (after cleared (eventLog oldRun) (N 2).val).val = 0
    rw [ho.outside _ (by omega) (by omega)]
    change (after mem (eventLog clear) (N 2).val).val = 0
    rw [hcZero _ (by omega) (by omega)]
    rfl
  obtain ⟨newRun,hnRun,hn,_,hnLen,hnCost⟩ :=
    prefixPass_run hnReg (by omega) hNewSum hnW hnZ
  refine ⟨clear, oldRun, newRun, ⟨hcRun, hoRun, hnRun, hcLen, hoLen, hnLen, ?_, ?_⟩, ?_⟩
  · simp only [List.map_append, List.sum_append]
    rw [sum_constant_cost _ clear 1 (fun r hr => (hcCost r hr).1),
      sum_constant_cost _ oldRun 4 (fun r hr => (hoCost r hr).1),
      sum_constant_cost _ newRun 4 (fun r hr => (hnCost r hr).1), hcLen, hoLen, hnLen]
    omega
  · simp only [List.map_append, List.sum_append]
    rw [sum_constant_cost _ clear 8 (fun r hr => (hcCost r hr).2),
      sum_constant_cost _ oldRun 14 (fun r hr => (hoCost r hr).2),
      sum_constant_cost _ newRun 14 (fun r hr => (hnCost r hr).2), hcLen, hoLen, hnLen]
    omega
  · change Prepared oldBase newBase B old new mem (after oldDone (eventLog newRun))
    have hkeepCount (x : ℕ) (hx : B.val + 2 ≤ x)
        (hx' : x < B.val + 2 + old.length + new.length) :
        after oldDone (eventLog newRun) x = 0 := by
      rw [hn.outside _ (by omega) (by omega)]
      change after cleared (eventLog oldRun) x = 0
      rw [ho.outside _ (by omega) (by omega)]
      exact hcZero x (by omega) (by omega)
    constructor
    · intro i hi
      rw [hn.outside _ (by omega) (by omega)]
      exact ho.widths i hi
    · exact hn.widths
    · intro i hi
      rw [hn.outside _ (by omega) (by omega)]
      simpa only [ho₁] using ho.starts i hi
    · simpa only [hn₁] using hn.starts
    · intro i hi
      exact hkeepCount _ (by omega) (by omega)
    · intro j hj
      exact hkeepCount _ (by omega) (by omega)
    · rw [hn.outside _ (by omega) (by omega)]
      simpa only [ho₂, List.take_length] using ho.total
    · simpa only [hn₂, List.take_length] using hn.total
    · intro x hx
      rw [hn.outside _ (by omega) (by omega)]
      change after cleared (eventLog oldRun) x = mem x
      rw [ho.outside _ (by omega) (by omega)]
      exact hcOutside x (by omega)

end CompressorRecords.SliceRAM

end VPVNP
end Computability
end OAI
