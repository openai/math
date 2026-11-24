import OAI.Computability.VPVNP.PairTraversalControllerFormula
import OAI.Computability.VPVNP.PairTraversalControllerInputs
import OAI.Computability.VPVNP.PairTraversalControllerOrdinal

/-!
# Readback of the traversal controller's loaded register bank

The register formulas read the level headers with the packed persistent
ordinal. Their two branchless count selections use self-division and
subtraction in the word ring. This also accounts for the initial-only
schedule and for the final controller sentinel.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalController

open BurstRAM PrivateRAM CompressorRecords PhaseRecipe
open TraversalControllerInputs TraversalControllerOrdinal
open scoped Fin.CommRing

variable {w : ℕ}

/-- The meanings of the eighteen loaded registers. The fiber worker executes
at a positive layer index. Its four producer fields are loaded also at index zero. -/
structure Readback (pub : Fin 11 → Word w) (m : Memory w) (L N p i : ℕ)
    (rs : Fin R → Word w) : Prop where
  site : rs (value 0) = (i : Word w)
  phase : rs (value 1) = (p : Word w)
  levels : rs (value 2) = (L : Word w)
  twice : rs (value 3) = ((2 * L : ℕ) : Word w)
  count : rs (value 4) = siteCount pub m (p % L)
  index : rs (value 5) = ((p % L : ℕ) : Word w)
  zero : rs (value 6) = 0
  next : rs (value 7) = (pack N p (i + 1) : Word w)
  reset : rs (value 8) = (pack N (p + 1) 0 : Word w)
  role : rs ∘ roleAlloc.words (by decide : 4 ≤ 6) = tagParams pub m (p % L)
  leaf : rs ∘ leafAlloc.words (by decide : 2 ≤ 6) = leafParams pub m
  fiberHeader : ∀ j : Fin 4, rs (fiberAlloc.bank (j.castLE (by decide))) =
    fiberParams pub m (p % L - 1) (j.castLE (by decide))
  fiber : p % L ≠ 0 → rs ∘ fiberAlloc.bank = fiberParams pub m (p % L - 1)

/-- Reading the operand bank from the terminal and level headers gives every
dispatch operand and worker parameter, including the next-state words. -/
theorem readback (pub : Fin 11 → Word w) (m : Memory w) (L N p i : ℕ)
    (rs : Fin R → Word w) (hLevels : (terminalField pub m 1).val = L)
    (hSites : (siteCount pub m 0).val = N) (hPos : 0 < L) (hDigit : i ≤ N)
    (hPitch : N + 1 < 2 ^ w) (hState : pack N p i < 2 ^ w)
    (loaded : ∀ t, rs (value t) = (formulas t).eval (recipePub pub) (pack N p i : Word w) m) :
    Readback pub m L N p i rs := by
  let ev := Expr.eval (recipePub pub) (pack N p i : Word w) m
  have hterm (d : ℕ) : ev (term d) = terminalField pub m d := rfl
  have hlevel {j : Expr} {n : ℕ} (hj : ev j = (n : Word w)) (d : ℕ) :
      ev (level j d) = levelField pub m n d := by
    change m (terminalField pub m 16 + ev j * terminalField pub m 17 + (d : Word w)).val = _
    rw [hj]
    rfl
  have hlevelZero := @hlevel (.lit 0) 0 rfl
  have hL : ev levels = (L : Word w) := by
    change terminalField pub m 1 = _
    rw [← hLevels]
    exact (Fin.ofNat_val_eq_self _).symm
  have fitL : L < 2 ^ w := hLevels ▸ (terminalField pub m 1).isLt
  have hN : ev initialSites = siteCount pub m 0 := by
    change ev (level (.lit 0) 21) + BinaryOp.div.eval 1 (ev levels) *
      (ev (term 7) - ev (level (.lit 0) 21)) = _
    rw [hlevelZero, hL, one_div_levels hPos fitL, hterm, siteCount, hLevels]
    by_cases h : L = 1 <;> simp [h]
  have hNcast : ev initialSites = (N : Word w) := by
    rw [hN, ← hSites]
    exact (Fin.ofNat_val_eq_self _).symm
  have hpitch : ev pitch = ((N + 1 : ℕ) : Word w) := by
    change ev initialSites + 1 = _
    rw [hNcast, Nat.cast_add, Nat.cast_one]
  obtain ⟨hquot, hrem⟩ := decode_of_fit hDigit hState hPitch
  have hphase : ev phaseLevel = (p : Word w) := by
    change BinaryOp.div.eval (pack N p i : Word w) (ev pitch) = _
    rwa [hpitch]
  have hsite : ev site = (i : Word w) := by
    change BinaryOp.mod.eval (pack N p i : Word w) (ev pitch) = _
    rwa [hpitch]
  have fitP : p < 2 ^ w := ((Nat.le_mul_of_pos_right p (Nat.succ_pos N)).trans
    (Nat.le_add_right _ i)).trans_lt hState
  obtain ⟨hidx, hflag, hprev⟩ := index_words hPos fitL fitP
  have hj : ev index = ((p % L : ℕ) : Word w) := by
    change BinaryOp.mod.eval (ev phaseLevel) (ev levels) = _
    rwa [hphase, hL]
  have hnz : ev positiveIndex = if p % L = 0 then 0 else 1 := by
    change BinaryOp.div.eval (BinaryOp.mod.eval (ev phaseLevel) (ev levels))
      (BinaryOp.mod.eval (ev phaseLevel) (ev levels)) = _
    rwa [hphase, hL]
  have hp : ev previous = ((p % L - 1 : ℕ) : Word w) := by
    change BinaryOp.sub.eval (BinaryOp.mod.eval (ev phaseLevel) (ev levels))
      (BinaryOp.div.eval (BinaryOp.mod.eval (ev phaseLevel) (ev levels))
        (BinaryOp.mod.eval (ev phaseLevel) (ev levels))) = _
    rwa [hphase, hL]
  have hc : ev count = siteCount pub m (p % L) := by
    change ev initialSites + ev positiveIndex * (ev (level previous 22) - ev initialSites) = _
    rw [hN, hnz, hlevel hp]
    cases h : p % L with
    | zero => simp
    | succ j => simp [siteCount]
  have ht : ev (levels.add levels) = ((2 * L : ℕ) : Word w) := by
    change ev levels + ev levels = _
    rw [hL, two_mul, Nat.cast_add]
  have hnext : ev (Expr.state.add (.lit 1)) = (pack N p (i + 1) : Word w) := by
    change (pack N p i : Word w) + 1 = _
    simp [pack, add_assoc]
  have hreset : ev ((phaseLevel.add (.lit 1)).mul pitch) = (pack N (p + 1) 0 : Word w) := by
    change (ev phaseLevel + 1) * ev pitch = _
    rw [hphase, hpitch]
    simp [pack]
  refine ⟨(loaded 0).trans hsite, (loaded 1).trans hphase, (loaded 2).trans hL,
    (loaded 3).trans ht, (loaded 4).trans hc, (loaded 5).trans hj, loaded 6,
    (loaded 7).trans hnext, (loaded 8).trans hreset, ?_, ?_, ?_, ?_⟩
  · funext j
    apply (loaded (roleFields (j.castLE (by decide)))).trans
    fin_cases j <;> first | exact hterm _ | exact hlevel hj _
  · funext j
    apply (loaded (leafFields (j.castLE (by decide)))).trans
    fin_cases j <;> first | exact hterm _ | exact hlevelZero _
  · intro j
    apply (loaded (fiberFields (j.castLE (by decide)))).trans
    fin_cases j <;> exact hlevel hp _
  · intro hpos
    have he : p % L - 1 + 1 = p % L := by omega
    funext j
    apply (loaded (fiberFields j)).trans
    fin_cases j <;> first | exact hlevel hp _ | exact hterm _ | skip
    change ev (level index 14) = levelField pub m (p % L - 1 + 1) 14
    rw [he]
    exact hlevel hj 14

end PairSimulation.TraversalController

end VPVNP
end Computability
end OAI
