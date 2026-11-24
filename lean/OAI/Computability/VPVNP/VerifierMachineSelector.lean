import OAI.Computability.BinPacking.CookLevin.ConfigIndex
import OAI.Computability.VPVNP.VerifierMachineSimulation
import OAI.Computability.VPVNP.VerifierMachineDecodeWire

/-!
# Selecting one transition from the decoded program

The current state and the two symbols under the heads determine a row. The next witness
bit selects its branch. The disjunction tests every possible instruction in that slot
against a Boolean predicate on its fields. It returns false for a halted state, a missing
branch, or an instruction failing the predicate.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace UniversalMachine

open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open VPVNP.VerifierMachineDecode

/-- Represent an instruction in the fixed range allocated for an input of length `n`. -/
def instructionKey {e n : ℕ} (h : e ≤ n) (a : Instruction e) : InstructionKey n :=
  (a.target.castLE (by omega), a.firstSymbol, a.firstMove, a.secondSymbol, a.secondMove)

theorem keyMatches_iff {e n : ℕ} (h : e ≤ n) (a : Instruction e) (k : InstructionKey n) :
    KeyMatches k a ↔ instructionKey h a = k := by
  rcases k with ⟨q, x, u, y, v⟩
  simp [KeyMatches, instructionKey, Prod.mk.injEq, Fin.ext_iff]

private abbrev SelectIndex (n : ℕ) := Fin n × Symbol × Symbol × InstructionKey n

private def SelectIndex.state {n : ℕ} (z : SelectIndex n) : Fin (n + 2) :=
  ⟨z.1.val + 2, by have := z.1.isLt; omega⟩

private def SelectIndex.row {n : ℕ} (z : SelectIndex n) : Fin (9 * n) :=
  ⟨z.1.val * 9 + z.2.1.val * 3 + z.2.2.1.val, by
    have := z.1.isLt
    have := z.2.1.isLt
    have := z.2.2.1.isLt
    omega⟩

variable {ι : Type*} {n r : ℕ}
variable (slots : Fin (9 * n) → Bool → InstructionKey n → Expr ι)
variable (reg : WindowRegister n r → Expr ι) (choice : Expr ι) (f : InstructionKey n → Bool)

private def selectTerm (z : SelectIndex n) : Expr ι :=
  .and (reg (.inl z.state))
    (.and (reg (.inr (false, windowCenter r, z.2.1)))
      (.and (reg (.inr (true, windowCenter r, z.2.2.1)))
        (.and (.const (f z.2.2.2))
          (Expr.mux choice (slots z.row true z.2.2.2) (slots z.row false z.2.2.2)))))

/-- Test whether the instruction selected by the current state, scanned symbols, and branch bit
satisfies the supplied predicate. -/
noncomputable def selectedExpr : Expr ι :=
  Expr.disjoin (Finset.univ.toList.map (selectTerm slots reg choice f))

private def currentRow {e : ℕ} (c : WindowConfig e r) : ℕ :=
  (c.state.val - 2) * 9 + (c.firstTape (windowCenter r)).val * 3 +
    (c.secondTape (windowCenter r)).val

private theorem rowInstruction_eq_chosen {e : ℕ} (row : Branches e) (bit : Bool) :
    rowInstruction row bit = chosenInstruction row bit := by
  cases row <;> cases bit <;> rfl

private theorem windowInstruction_some (p : Program) (c : WindowConfig p.extra r)
    (bit : Bool) (a : Instruction p.extra) :
    windowInstruction p c bit = some a ↔ 2 ≤ c.state.val ∧
      ∃ row, p.rows[currentRow c]? = some row ∧ rowInstruction row bit = some a := by
  by_cases h : 2 ≤ c.state.val
  · simp only [windowInstruction, h, ite_true, true_and, ← rowInstruction_eq_chosen]
    change rowInstruction (p.rows[currentRow c]?.getD .stop) bit = some a ↔ _
    cases hr : p.rows[currentRow c]? with
    | none => simp [rowInstruction]
    | some b => simp
  · simp [windowInstruction, h]

private theorem eval_selectTerm (z : SelectIndex n) (input : ι → Bool) (p : Program)
    (c : WindowConfig p.extra r) (bit : Bool)
    (hslot : ∀ i b k, (slots i b k).eval input = true ↔ wireHolds p (.slot i b k))
    (hreg : ∀ i, (reg i).eval input = registerEncoding c i) (hchoice : choice.eval input = bit) :
    (selectTerm slots reg choice f z).eval input = true ↔
      c.state.val = z.1.val + 2 ∧ c.firstTape (windowCenter r) = z.2.1 ∧
      c.secondTape (windowCenter r) = z.2.2.1 ∧ f z.2.2.2 = true ∧
      wireHolds p (.slot z.row bit z.2.2.2) := by
  cases bit <;>
    simp [selectTerm, Expr.eval, Expr.eval_mux, hreg, hchoice, hslot, registerEncoding,
      SelectIndex.state]

theorem eval_selectedExpr (input : ι → Bool) (p : Program) (h : p.extra ≤ n)
    (c : WindowConfig p.extra r) (bit : Bool)
    (hslot : ∀ i b k, (slots i b k).eval input = true ↔ wireHolds p (.slot i b k))
    (hreg : ∀ i, (reg i).eval input = registerEncoding c i) (hchoice : choice.eval input = bit) :
    (selectedExpr slots reg choice f).eval input =
      (windowInstruction p c bit).any (fun a => f (instructionKey h a)) := by
  apply Bool.eq_iff_iff.mpr
  rw [selectedExpr, Expr.eval_disjoin_true, Option.any_eq_true]
  constructor
  · rintro ⟨t, ht, ht'⟩
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hq, hx, hy, hf, row, a, hrow, ha, hk⟩ :=
      (eval_selectTerm slots reg choice f z input p c bit hslot hreg hchoice).mp ht'
    have hr : currentRow c = z.row.val := by simp [currentRow, SelectIndex.row, hq, hx, hy]
    exact ⟨a, (windowInstruction_some p c bit a).mpr
      ⟨by omega, row, hr ▸ hrow, ha⟩, (keyMatches_iff h a _).mp hk ▸ hf⟩
  · rintro ⟨a, ha, hf⟩
    obtain ⟨hrun, row, hrow, hbranch⟩ := (windowInstruction_some p c bit a).mp ha
    let q : Fin n := ⟨c.state.val - 2, by have := c.state.isLt; omega⟩
    let z : SelectIndex n :=
      (q, c.firstTape (windowCenter r), c.secondTape (windowCenter r), instructionKey h a)
    refine ⟨selectTerm slots reg choice f z, List.mem_map.mpr ⟨z, by simp, rfl⟩,
      (eval_selectTerm slots reg choice f z input p c bit hslot hreg hchoice).mpr ?_⟩
    exact ⟨by change c.state.val = c.state.val - 2 + 2; omega, rfl, rfl, hf,
      row, a, hrow, hbranch, (keyMatches_iff h a _).mpr rfl⟩

/-- Each possible source and instruction contributes one constant-depth selector term. -/
theorem size_selectedExpr
    (slots : Fin (9 * n) → Bool → InstructionKey n → Expr ι)
    (reg : WindowRegister n r → Expr ι) (choice : Expr ι) (f : InstructionKey n → Bool)
    (C : ℕ) (hslot : ∀ i b k, (slots i b k).size ≤ C) (hreg : ∀ i, (reg i).size ≤ C)
    (hchoice : choice.size ≤ C) : (selectedExpr slots reg choice f).size ≤
      20000 * (n + 2) ^ 2 * (C + 1) := by
  unfold selectedExpr
  have hb : ∀ e ∈ Finset.univ.toList.map (selectTerm slots reg choice f), e.size ≤ 7 * C + 9 := by
    intro e he
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp he
    simp only [selectTerm, Expr.mux, Expr.size]
    have hq := hreg (.inl z.state)
    have h₁ := hreg (.inr (false, windowCenter r, z.2.1))
    have h₂ := hreg (.inr (true, windowCenter r, z.2.2.1))
    have ht := hslot z.row true z.2.2.2
    have hf := hslot z.row false z.2.2.2
    omega
  have hs := Expr.size_disjoin_le _ _ hb
  simp only [List.length_map, Finset.length_toList, Finset.card_univ, SelectIndex,
    InstructionKey, Symbol, Fintype.card_prod, Fintype.card_fin] at hs
  exact hs.trans (by ring_nf; omega)

end UniversalMachine

end VPVNP
end Computability
end OAI
