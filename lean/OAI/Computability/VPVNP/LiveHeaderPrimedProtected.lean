import OAI.Computability.VPVNP.LiveHeaderPrimedStages
import OAI.Computability.VPVNP.LiveHeaderProtectedCore

/-!
# Protected memory in the primed header stages

The digit guard bounds both shifted output addresses, even for an arbitrary
persistent state. The digit and borrow values read from memory can be arbitrary
words since they only determine the data stored at those addresses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram.PrimedStages

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM LiveHeaderSchedule
open LiveHeader.PrimedGroupIndices
open scoped Fin.CommRing

variable {w : ℕ}

/-- Every successful initialization call preserves all words below the stage tag. -/
theorem init_protected (s : Sizes) (base : ℕ) (fit : limit s base ≤ 2^w)
    (fuel : ℕ) (st : Word w) (m : Memory w) (bits : List Bool) (rep : Report w)
    (h : let P := ((stageTemplate .primedInit).2.instantiate w (rowData w s base .primedInit)).program
         execute P fuel (P.start st) m bits = some rep) :
    ∀ a < base, after m rep.events a = m a := by
  let pub := operands w s base
  have hrow : rowData w s base .primedInit ∘ includeFin (by decide : 4 ≤ 17) = pub := by
    funext j
    fin_cases j <;> rfl
  have hentry := entry_start ((lines setup (by decide)).template none) (by decide) (by decide)
    (rowData w s base .primedInit) fuel st m bits
  rw [hrow] at hentry
  obtain ⟨_,mem,hexec,_⟩ := (Flow.template_execute_iff (lines setup (by decide)) none pub st
    (fun _ => 0) (fun _ => 0) m fuel bits rep).mp (hentry.symm.trans h)
  have ht := (PrimedCounter.Admin.exec_lines_iff_trace (by decide : setup ≠ [])).mp hexec
  rw [LiveHeader.trace_after ht]
  have hm : initialized pub m = mem := by
    simp (config := { decide := true }) [setup, trace, Op.effect, Function.update] at ht
    exact ht.2.2
  rw [← hm]
  obtain ⟨_,hl,hr,hb,_,_⟩ := operand_values s base fit
  intro a ha
  have l : a ≠ leftIndexBase s base := by unfold leftIndexBase populationAddr highAddr indexBase; omega
  have r : a ≠ rightIndexBase s base := by unfold rightIndexBase leftIndexBase populationAddr highAddr indexBase; omega
  have b : a ≠ borrowAddr base := by unfold borrowAddr; omega
  simp only [initialized, pub, writeMemory, hb, hl, hr, ite_eq_right b, ite_eq_right r, ite_eq_right l]

private theorem digit_writes (pub : Fin 4 → Word w) (st : Word w) (m : Memory w) :
    let P := ((template digit 11).instantiate w pub).program
    ∃ r : Report w, execute P 21 (P.start st) m [] = some r ∧
      ∀ a, a ≠ (pub 1 + (st+1)).val → a ≠ (pub 2 + (st+1)).val → a ≠ (pub 3).val →
        after m r.events a = m a := by
  dsimp only
  let x := m (pub 0 + st).val
  let c := m (pub 3).val
  let b := (1-x)*c
  let es : List (Event w) := [.tick, .tick, .tick, .tick, .tick, .read (pub 0 + st) x,
    .tick, .tick, .tick, .tick, .tick, .read (pub 3) c, .tick, .tick, .tick, .tick, .tick,
    .write (pub 1 + (st + 1)) (x - c + b + b), .write (pub 2 + (st + 1)) x, .write (pub 3) b]
  refine ⟨⟨es, some (st+1)⟩, ?_, ?_⟩
  · change execute ((template digit 11).instantiate w pub).program (1 + digit.length)
      ⟨_,st,fun _ => 0,fun _ => 0⟩ m [] = _
    rw [execute_template, run_eq_trace]
    simp (config := { decide := true }) [digit, trace, Op.effect, Function.update, es, x, c, b,
      show BinaryOp.add.eval = (· + · : Word w → Word w → Word w) from rfl,
      show BinaryOp.sub.eval = (· - · : Word w → Word w → Word w) from rfl,
      show BinaryOp.mul.eval = (· * · : Word w → Word w → Word w) from rfl]
  · intro a hl hr hb
    simp only [es, after, List.foldl_cons, List.foldl_nil, update, writeMemory, hl, hr, hb,
      ite_false]

private theorem shifted_addresses (s : Sizes) (base : ℕ) (fit : limit s base ≤ 2^w)
    (st : Word w) (active : st < ((s.h+1 : ℕ) : Word w)) :
    let pub := operands w s base
    base ≤ (pub 1 + (st+1)).val ∧ base ≤ (pub 2 + (st+1)).val ∧ base ≤ (pub 3).val := by
  dsimp only
  let pub := operands w s base
  obtain ⟨-,hl,hr,hb,-,hcap⟩ := operand_values s base fit
  have layout := layout_of_fit s base fit
  have hc : st.val < s.h+1 := by
    change st.val < (s.h+1) % (2^w) at active
    rwa [Nat.mod_eq_of_lt hcap] at active
  have hleft := offset_val (pub 1) (st.val+1) (by have := layout.leftFit; dsimp [pub]; omega)
  have hright := offset_val (pub 2) (st.val+1) (by have := layout.rightFit; dsimp [pub]; omega)
  have hst : (st.val : Word w) = st := Fin.ext (Nat.mod_eq_of_lt st.isLt)
  simp only [Nat.cast_add, Nat.cast_one, hst] at hleft hright
  change base ≤ (pub 1 + (st+1)).val ∧ base ≤ (pub 2 + (st+1)).val ∧ base ≤ (pub 3).val
  rw [hleft,hright]
  dsimp only [pub]
  rw [hl,hr,hb]
  simp only [rightIndexBase,leftIndexBase,populationAddr,highAddr,indexBase,borrowAddr]
  omega

/-- Every successful guarded digit call preserves the protected memory below the stage tag. -/
theorem digits_protected (s : Sizes) (base : ℕ) (fit : limit s base ≤ 2^w)
    (fuel : ℕ) (st : Word w) (m : Memory w) (bits : List Bool) (rep : Report w)
    (h : let P := ((stageTemplate .primedDigits).2.instantiate w (rowData w s base .primedDigits)).program
         execute P fuel (P.start st) m bits = some rep) :
    ∀ a < base, after m rep.events a = m a := by
  let pub := operands w s base
  let bound : Word w := (s.h+1 : ℕ)
  have hrow : rowData w s base .primedDigits ∘ includeFin (by decide : 5 ≤ 17) =
      LiveHeaderBounded.publicData pub bound := by
    funext j
    fin_cases j <;> rfl
  have he := entry_start (LiveHeaderBounded.bounded (template digit 11)) (by decide) (by decide)
    (rowData w s base .primedDigits) fuel st m bits
  rw [hrow] at he
  intro a ha
  apply LiveHeaderBounded.frame_any (template digit 11) pub bound fuel st m bits rep (he.symm.trans h) a
  intro f r active run
  obtain ⟨out,hex,frame⟩ := digit_writes pub st m
  obtain ⟨_,rfl⟩ := execute_empty_forces_anyFuel hex run
  obtain ⟨hl,hr,hb⟩ := shifted_addresses s base fit st active
  exact frame a (ha.trans_le hl).ne (ha.trans_le hr).ne (ha.trans_le hb).ne

end LiveHeaderProgram.PrimedStages

end VPVNP
end Computability
end OAI
