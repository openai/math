import OAI.Computability.BorderVNP.CoverAddressCoding
import OAI.Computability.BorderVNP.CoverDeckTower

/-!
# Literal low-residue tables

The low residue is drawn from a fixed finite set. A shared first layer tests equality
with each possible key. Each output bit then reads its row from the fixed displacement
table. The cost counts every comparison and each output selector.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open BorderVNP.StackFrame
open VPVNP.VerifierNetwork (Frame)

private noncomputable def keyTest {σ : Type*} [Fintype σ] (key : σ → Bool) : Expr σ :=
  .not (Expr.disjoin (Finset.univ.toList.map fun i =>
    if key i then .not (.input i) else .input i))

private theorem keyTest_eval {σ : Type*} [Fintype σ] (key x : σ → Bool) :
    (keyTest key).eval x = true ↔ x = key := by
  have mismatch (i : σ) :
      ((if key i then .not (.input i) else .input i : Expr σ).eval x = true) ↔ x i ≠ key i := by
    cases key i <;> cases hx : x i <;> simp [hx,Expr.eval]
  simp only [keyTest,Expr.eval,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,Expr.eval_disjoin_true,
    List.mem_map,Finset.mem_toList,Finset.mem_univ,true_and,exists_exists_eq_and,mismatch,
    not_exists,not_not]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

private theorem keyTest_size {σ : Type*} [Fintype σ] (key : σ → Bool) :
    (keyTest key).size ≤ 3*Fintype.card σ+2 := by
  unfold keyTest
  simp only [Expr.size]
  apply (Nat.add_le_add_right (Expr.size_disjoin_le _ 2 ?_) 1).trans
  · simp [mul_comm]
  · intro e he
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
    cases key i <;> simp [Expr.size]

private noncomputable def tableBit {α ρ : Type*} [Fintype α] (table : α → ρ → Bool) (j : ρ) :
    Expr α := Expr.disjoin (Finset.univ.toList.map fun a => if table a j then .input a else .const false)

private theorem tableBit_eval {α ρ : Type*} [Fintype α] (table : α → ρ → Bool) (j : ρ)
    (hit : α → Bool) (a : α) (h : ∀ b, hit b = true ↔ b = a) :
    (tableBit table j).eval hit = table a j := by
  have term (b : α) :
      ((if table b j then .input b else .const false : Expr α).eval hit = true) ↔
        table b j = true ∧ b = a := by
    cases table b j <;> simp [Expr.eval,h]
  apply Bool.eq_iff_iff.mpr
  simp [tableBit,Expr.eval_disjoin_true,term]

private theorem tableBit_size {α ρ : Type*} [Fintype α] (table : α → ρ → Bool) (j : ρ) :
    (tableBit table j).size ≤ 2*Fintype.card α+1 := by
  apply (Expr.size_disjoin_le _ 1 ?_).trans
  · simp [mul_comm]
  · intro e he
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
    cases table i j <;> rfl

/-- One shared equality test for each encoded key, followed by a table-bit
selection for each output. The gate bound is independent of the table contents. -/
theorem lookupFrame {α σ ρ : Type*} [Fintype α] [Fintype σ] [Fintype ρ]
    (encode : α → σ → Bool) (injective : Function.Injective encode) (table : α → ρ → Bool) :
    ∃ f : Frame σ ρ,
      f.size ≤ Fintype.card α * (3*Fintype.card σ+2) + Fintype.card ρ * (2*Fintype.card α+1) ∧
      ∀ a, f.eval (encode a) = table a := by
  let selectors := (Frame.initial (id : σ → σ)).step (fun a => keyTest (encode a))
  refine ⟨selectors.step (tableBit table), ?_, ?_⟩
  · have hs := Frame.step_size_le (Frame.initial id) (fun a => keyTest (encode a)) _
      (fun a => keyTest_size (encode a))
    exact (Frame.step_size_le selectors (tableBit table) _ (tableBit_size table)).trans
      (Nat.add_le_add_right (by simpa [selectors] using hs) _)
  · intro a
    have hi : (Frame.initial id).eval (encode a) = encode a := funext fun _ => by simp
    have he (b : α) : selectors.eval (encode a) b = true ↔ b = a := by
      dsimp only [selectors]
      rw [Frame.step_eval,hi,keyTest_eval,injective.eq_iff,eq_comm]
    funext j
    rw [Frame.step_eval,tableBit_eval table j _ a he]

/-- Boolean lookup of an arbitrary displacement at a fixed low level. All high-level
output bits share the same low-level key comparisons. -/
theorem offsetFrame (k l : ℕ) (offset : Deck k → Deck l) :
    ∃ f : Frame (Slots (width k)) (Slots (width l)),
      f.size ≤ Fintype.card (Deck k) * (9*width k + 2) +
        3*width l * (2*Fintype.card (Deck k) + 1) ∧
      ∀ x, f.eval (deckWires k x) = deckWires l (offset x) := by

  obtain ⟨f,hf,he⟩ := lookupFrame (deckWires k) (deckWires_injective k) (fun x => deckWires l (offset x))
  refine ⟨f,?_,he⟩
  simpa [Slots,mul_assoc,mul_comm,mul_left_comm] using hf

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
