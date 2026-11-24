import OAI.Computability.VPVNP.LiveEvaluatorGroup

/-!
# Raw cell words on successful live evaluator calls

On a successful group the source check examines every word, even the
overwritten head cell. Destination words are either zero (for a halt) or
equal to a legal written symbol. The old-cell permutation covers every
destination, so an accepting computation forces both configuration arrays
to have canonical symbol fields.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorGroup

open BurstRAM (Word Memory)
open UniversalMachine (Symbol Instruction Program WindowCell)
open LiveEvaluatorEncoding (Code TapeWindow ConfigWindow)
open LiveEvaluatorRAM (ConfigAt ActionAt PrepLayout cellTest destination destination_val_of_limbs)
open LiveEvaluatorRAM.Schedule
open LiveEvaluatorStep (cellDestination cellDestination_surjective)
open scoped Fin.CommRing

variable {w M extra : ℕ}

/-- Read the machine word for a given tape cell from the physical configuration array. -/
def cellWord (m : Memory w) (base : Word w) (side : Bool) (i : WindowCell M) : Word w :=
  m (baseOf base M side + (i.val : Word w)).val

/-- The actual state and symbol words determine a canonical cut configuration
if the state and symbol ranges and halt padding pass. -/
theorem configAt_of_valid (m : Memory w) (base : Word w)
    (hp : 0 < (m base.val).val) (hs : (m base.val).val < extra + 2)
    (cells : ∀ side (i : WindowCell M), (cellWord m base side i).val < 3 ∧
      ((m base.val).val = 1 → (cellWord m base side i).val = 0)) :
    ∃ c : Code extra M, ConfigAt m base c := by
  by_cases ha : (m base.val).val = 1
  · refine ⟨.accepted, ha, fun i => (cells false i).2 ha, fun i => (cells true i).2 ha⟩
  · let t (side : Bool) : TapeWindow M :=
      ⟨fun i => ⟨(cellWord m base side i).val, (cells side i).1⟩⟩
    let c : ConfigWindow extra M := ⟨⟨_, hs⟩, t false, t true⟩
    exact ⟨.running c (by change 2 ≤ (m base.val).val; omega), rfl, fun _ => rfl, fun _ => rfl⟩

theorem configAt_congr_block {m m' : Memory w} {base : Word w} {c : Code extra M}
    (hc : ConfigAt m base c)
    (h : ∀ i < calls M, m (base + (i : Word w)).val = m' (base + (i : Word w)).val) :
    ConfigAt m' base c := by
  constructor
  · have he := h 0 (by simp [calls])
    simp at he
    exact (congrArg Fin.val he).symm.trans hc.state
  · intro i
    have he := h (1 + i.val) (by unfold calls; omega)
    simpa [add_assoc] using (congrArg Fin.val he).symm.trans (by simpa [add_assoc] using hc.first i)
  · intro i
    have he := h (1 + (2*M+1) + i.val) (by unfold calls; omega)
    simpa [add_assoc] using (congrArg Fin.val he).symm.trans (by simpa [add_assoc] using hc.second i)

private theorem acceptedCellFacts (p : Program) (pub : Pub → Word w) (m : Memory w)
    (a : Instruction p.extra) (hl : PrepLayout p pub M) (hr : AllCells M p pub m)
    (hact : ActionAt m (pub 3) a.target.val a.firstSymbol a.firstMove a.secondSymbol a.secondMove)
    (htarget : (m (pub 2).val).val = a.target.val)
    (side : Bool) (i : WindowCell M) :
    let move := if side then a.secondMove else a.firstMove
    let j := if a.target.val = 1 then i else cellDestination move i
    ((cellWord m (pub 1) side i).val < 3 ∧
      ((m (pub 1).val).val = 1 → (cellWord m (pub 1) side i).val = 0)) ∧
    ((cellWord m (pub 2) side j).val < 3 ∧
      ((m (pub 2).val).val = 1 → (cellWord m (pub 2) side j).val = 0)) := by
  dsimp only
  let st : Word w := (cellCursor side i : Word w)
  let r := bank pub (fun _ => 0) m side i
  have hval : st.val = cellCursor side i :=
    Nat.mod_eq_of_lt ((cellCursor_lt_calls side i).trans (calls_fit hl))
  have hs : st ≠ 0 := by
    intro h
    have : cellCursor side i = 0 := hval.symm.trans (congrArg Fin.val h)
    simp [cellCursor] at this
  have he : cellTest r m := (noninitial_call_iff p pub hs _ m).mp (hr side i)
  obtain ⟨hz, h₁, h₃, h₅, h₆, h₇, _, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆⟩ :=
    bank_operands pub (fun _ => 0) m side i hl.radius (calls_fit hl)
  change r 0 = _ at hz
  change r 1 = _ at h₁
  change r 3 = _ at h₃
  change r 5 = _ at h₅
  change r 6 = _ at h₆
  change r 7 = _ at h₇
  change r 12 = _ at h₁₂
  change r 13 = _ at h₁₃
  change r 14 = _ at h₁₄
  change r 15 = _ at h₁₅
  change r 16 = _ at h₁₆
  let move := if side then a.secondMove else a.firstMove
  let write := if side then a.secondSymbol else a.firstSymbol
  have hfour : 4 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide : 0 < 2) hl.width
  have hzero : (r 0).val = 0 := by rw [hz]; rfl
  have hone : (r 1).val = 1 := by rw [h₁]; exact Nat.mod_eq_of_lt (by omega : 1 < 2 ^ w)
  have hthree : (r 3).val = 3 := by rw [h₃]; exact Nat.mod_eq_of_lt (by omega : 3 < 2 ^ w)
  have hmax : (r 12).val = 2*M := by
    rw [h₁₂, Fin.val_natCast, Nat.mod_eq_of_lt]
    have := calls_fit hl
    unfold calls at this
    omega
  have hindex : (r 13).val = i.val := by
    rw [h₁₃, Fin.val_natCast, Nat.mod_eq_of_lt]
    have := calls_fit hl
    unfold calls at this
    omega
  have hm : (r 7).val = move.val := by
    rw [h₇]
    cases side <;> simp only [move, writeAddr, Bool.false_eq_true, ↓reduceIte]
    · rw [show pub 3 + 1 + 1 = pub 3 + 2 by ring]
      exact hact.firstMoveVal
    · rw [show pub 3 + 3 + 1 = pub 3 + 4 by ring]
      exact hact.secondMoveVal
  have hw : (r 6).val = write.val := by
    rw [h₆]
    cases side <;> first | exact hact.firstWriteVal | exact hact.secondWriteVal
  have hs₁ : r 16 = r 1 ↔ (m (pub 1).val).val = 1 := by
    rw [Fin.ext_iff, hone, h₁₆]
  have ht₁ : r 5 = r 1 ↔ a.target.val = 1 := by
    rw [Fin.ext_iff, hone, h₅, hact.targetVal]
  have hsrc : m (r 14 + r 13).val = cellWord m (pub 1) side i := by
    rw [h₁₄, h₁₃]; rfl
  obtain ⟨hold, hout⟩ := he
  change (if r 16 = r 1 then m (r 14 + r 13).val = r 0 else m (r 14 + r 13).val < r 3) at hold
  rw [hsrc] at hold
  have valid : (cellWord m (pub 1) side i).val < 3 ∧
      ((m (pub 1).val).val = 1 → (cellWord m (pub 1) side i).val = 0) := by
    split at hold
    · have h := (congrArg Fin.val hold).trans hzero
      exact ⟨by omega, fun _ => h⟩
    · exact ⟨(show (cellWord m (pub 1) side i).val < (r 3).val from hold).trans_le hthree.le,
        fun h => False.elim (‹r 16 ≠ r 1› (hs₁.mpr h))⟩
  refine ⟨valid, ?_⟩
  by_cases hhalt : a.target.val = 1
  · simp only [hhalt, ite_true]
    rw [ite_eq_left (ht₁.mpr hhalt)] at hout
    have heq : (cellWord m (pub 2) side i).val = 0 := by
      rw [h₁₅, h₁₃] at hout
      exact (congrArg Fin.val hout).trans hzero
    exact ⟨by omega, fun _ => heq⟩
  · simp only [hhalt, ite_false]
    rw [ite_eq_right (fun h => hhalt (ht₁.mp h))] at hout
    obtain ⟨_, ho⟩ := hout
    let d := destination (r 0) (r 1) (r 12) (r 7) (r 13)
    have hd := destination_val_of_limbs _ _ _ _ _ move i hzero hone hmax hm hindex
    have hdc : d = ((cellDestination move i).val : Word w) := by rw [← hd, Fin.cast_val_eq_self]
    change m (r 15 + d).val = if r 13 = r 11 then r 6 else m (r 14 + r 13).val at ho
    rw [h₁₅, hdc, hsrc] at ho
    have hlt : (cellWord m (pub 2) side (cellDestination move i)).val < 3 := by
      split at ho
      · exact ((congrArg Fin.val ho).trans hw) ▸ write.isLt
      · exact congrArg Fin.val ho ▸ valid.1
    exact ⟨hlt, fun h => False.elim (hhalt (htarget ▸ h))⟩

/-- An occupied scratch instruction and successful scan force all old and
new tape fields to encode canonical evaluator symbols. -/
theorem rawCells_force_images (p : Program) (pub : Pub → Word w) (m : Memory w)
    (a : Instruction p.extra) (hl : PrepLayout p pub M) (hr : AllCells M p pub m)
    (hact : ActionAt m (pub 3) a.target.val a.firstSymbol a.firstMove a.secondSymbol a.secondMove)
    (hold : 0 < (m (pub 1).val).val ∧ (m (pub 1).val).val < p.extra + 2)
    (hpos : 0 < a.target.val) (htarget : (m (pub 2).val).val = a.target.val) :
    (∃ c : Code p.extra M, ConfigAt m (pub 1) c) ∧ (∃ c : Code p.extra M, ConfigAt m (pub 2) c) := by
  have h := acceptedCellFacts p pub m a hl hr hact htarget
  refine ⟨configAt_of_valid m (pub 1) hold.1 hold.2 (fun s i => (h s i).1), ?_⟩
  apply configAt_of_valid m (pub 2) (htarget ▸ hpos) (htarget ▸ a.target.isLt)
  intro side j
  by_cases ha : a.target.val = 1
  · simpa only [ha, ite_true] using (h side j).2
  · obtain ⟨i, rfl⟩ := cellDestination_surjective (if side then a.secondMove else a.firstMove) j
    simpa only [ha, ite_false] using (h side i).2

end LiveEvaluatorGroup

end VPVNP
end Computability
end OAI
