import OAI.Computability.BorderVNP.PackedSewnFragmentPairSpec

/-! # Canonical zero source word for a clamped physical interval -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment

open ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {n w : ℕ}

private def zeroClamp (z : Pin n w) : Expr (Pin n w) :=
  match z.2 with
  | .inr (k,j) => if k = 3 then .and (.input (z.1,.inl true)) (.input (z.1,.inr (k,j))) else .input z
  | .inl _ => .input z

/-- A clamp writes a physical zero operand into its unused source position. -/
noncomputable def canonical (n w : ℕ) : Frame (Pin n w) (Pin n w) :=
  (Frame.initial id).step zeroClamp

/-- Only the existing source bits need one gate each to clear clamped words. -/
theorem canonical_size : (canonical n w).size ≤ n*(2+4*w)*3 := by
  have h (z : Pin n w) : (zeroClamp z).size ≤ 3 := by
    rcases z with ⟨i,c|⟨k,j⟩⟩
    · change 1 ≤ 3; decide
    · by_cases h : k=3 <;> simp [zeroClamp,h,StatementCircuit.Expr.size]
  simpa only [canonical,Frame.initial_size,Nat.zero_add,Pin,Column,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_bool,Fintype.card_fin] using Frame.step_size_le (Frame.initial (id : Pin n w → _)) zeroClamp 3 h

private theorem flags (x : Pin n w → Bool) (i : Fin n) (b : Bool) :
    (canonical n w).eval x (i,.inl b) = x (i,.inl b) := by
  simp [canonical,zeroClamp,StatementCircuit.Expr.eval]

private theorem values (x : Pin n w → Bool) (i : Fin n) (k : Fin 4) :
    word (fun j => (canonical n w).eval x (i,j)) k =
      if k=3 ∧ x (i,.inl true)=false then 0 else word (fun j => x (i,j)) k := by
  have zero : ∀ w, value (fun _ : Fin w => false) = 0 := by
    intro w
    induction w with
    | zero => rfl
    | succ w ih => simpa [value] using ih
  by_cases hk : k=3 <;> cases hb : x (i,.inl true) <;>
    simp [word,canonical,zeroClamp,StatementCircuit.Expr.eval,hk,hb,zero]

/-- Every nonsourced output has a literal numerical zero in its source column. -/
theorem canonical_clamp (x : Pin n w → Bool) (i : Fin n) (clamp : (canonical n w).eval x (i,.inl true)=false) :
    word (fun j => (canonical n w).eval x (i,j)) 3 = 0 := by
  rw [flags] at clamp
  simp [values,clamp]

/-- Clearing the ignored physical operand preserves the entire decoded chronology. -/
theorem canonical_list (x : Pin n w → Bool) : list ((canonical n w).eval x) = list x := by
  apply List.filterMap_congr
  intro i _
  simp only [active,parse,parseRow,flags,values]
  have h₀ : (0 : Fin 4) ≠ 3 := by decide
  have h₁ : (1 : Fin 4) ≠ 3 := by decide
  have h₂ : (2 : Fin 4) ≠ 3 := by decide
  by_cases h : x (i,.inl true) = true <;> simp [h,h₀,h₁,h₂]

end Packing.SewnField.Fragment

end BorderVNP
end Computability
end OAI
