import OAI.Computability.BorderVNP.CrossingFusionBinary
import OAI.Computability.VPVNP.OracleBinaryTarget

/-! # Checking the range of binary mode fields

The local path indices occupy fixed-width binary fields. This verifier rejects each
unused bit pattern, including all patterns when the label set is empty.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.FusionFlags

open VPVNP
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

variable {σ : Type*} {d M : ℕ}

/-- Decode a little-endian field without restricting it to valid mode labels. -/
noncomputable def decoded {a : ℕ} (bits : Fin a → Bool) : Fin (2^a) :=
  (RAMSerialization.wordBits a).symm bits

/-- The physical bits of a decoded field, including a field of width zero. -/
theorem decoded_bit {a : ℕ} (bits : Fin a → Bool) (b : Fin a) :
    (decoded bits).val.testBit b.val = bits b := by
  rw [LiveHeader.testBit_wordBits, decoded, Equiv.apply_symm_apply]

private def validOne (wire : Fin (Nat.clog 2 M) → σ) : Expr σ :=
  Expr.disjoin (List.ofFn fun j : Fin M => OracleBinaryTarget.expr wire j.val)

private theorem validOne_eval (wire : Fin (Nat.clog 2 M) → σ) (x : σ → Bool) :
    (validOne wire).eval x = true ↔ (decoded (x ∘ wire)).val < M := by
  rw [validOne, Expr.eval_disjoin_true]
  simp only [List.mem_ofFn, exists_exists_eq_and]
  have h (j : Fin M) : (OracleBinaryTarget.expr wire j.val).eval x =
      decide ((decoded (x ∘ wire)).val = j.val) :=
    OracleBinaryTarget.expr_eval wire j.val _ (decoded _).isLt x
      (fun i => (decoded_bit (x ∘ wire) i).symm)
  simp only [h, decide_eq_true_eq]
  exact ⟨fun ⟨j,hj⟩ => hj ▸ j.isLt, fun hj => ⟨⟨_,hj⟩,rfl⟩⟩

private theorem validOne_size (wire : Fin (Nat.clog 2 M) → σ) :
    (validOne wire).size ≤ M * (Nat.clog 2 M * 3 + 3) + 1 := by
  have hs := Expr.size_disjoin_le
    (List.ofFn fun j : Fin M => OracleBinaryTarget.expr wire j.val) (Nat.clog 2 M * 3 + 2)
    (fun e he => by obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he; exact OracleBinaryTarget.expr_size_le ..)
  simpa only [validOne, List.length_ofFn, Nat.add_assoc] using hs

/-- A range check on all mode indices, expressed in the ordinary shared verifier circuit. -/
def modeValidity (wire : Fin d → Fin (Nat.clog 2 M) → σ) : Expr σ :=
  .not (Expr.disjoin (List.ofFn fun i => .not (validOne (wire i))))

/-- The test accepts exactly the tuples of actual mode labels. -/
theorem modeValidity_eval (wire : Fin d → Fin (Nat.clog 2 M) → σ) (x : σ → Bool) :
    (modeValidity wire).eval x = true ↔ ∀ i, (decoded (x ∘ wire i)).val < M := by
  rw [modeValidity, Expr.eval, Bool.not_eq_true', Bool.eq_false_iff]
  change ¬ (_ = true) ↔ _
  rw [Expr.eval_disjoin_true]
  simp only [List.mem_ofFn, exists_exists_eq_and, Expr.eval, Bool.not_eq_true', not_exists,
    Bool.not_eq_false, validOne_eval]

/-- The range check is polynomial in the number, width and alphabet of the mode fields. -/
theorem modeValidity_size (wire : Fin d → Fin (Nat.clog 2 M) → σ) :
    (modeValidity wire).size ≤ d * (M * (Nat.clog 2 M * 3 + 3) + 3) + 2 := by
  have hs := Expr.size_disjoin_le
    (List.ofFn fun i => Expr.not (validOne (wire i))) (M * (Nat.clog 2 M * 3 + 3) + 2)
    (fun e he => by
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
      exact Nat.add_le_add_right (validOne_size _) _)
  simpa only [modeValidity, Expr.size, List.length_ofFn, Nat.add_assoc] using Nat.add_le_add_right hs 1

end Crossing.FusionFlags

end BorderVNP
end Computability
end OAI
