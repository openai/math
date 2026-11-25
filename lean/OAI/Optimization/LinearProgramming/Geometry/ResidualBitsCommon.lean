import OAI.Optimization.LinearProgramming.Geometry.UniformGramCore

/-! Numerical guard for the row projection and its residual difference. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace ResidualBitsCommon
open RAM Matrix
open scoped Matrix
variable {r n : ℕ}

def residualEntryBits (r n B : ℕ) : ℕ := 3 + 2*(3 + gramProjectorBits r n B)

theorem weaken {P R : ℚ → Prop} {D : Matrix (Fin r) (Fin n) ℚ}
    (h : UniformGramValues P D) (hpr : ∀ x, P x → R x) (hneg : ∀ x, R x → R (-x)) :
    UniformGramValues R D :=
  ⟨hpr _ h.zero, hpr _ h.one, hneg, fun i j u => hpr _ (h.gram i j u), hpr _ h.reciprocal,
    fun a k hk z => hpr _ (h.bird a k hk z), fun i j => hpr _ (h.inverse i j),
    fun i j u => hpr _ (h.left i j u), fun i j u => hpr _ (h.result i j u)⟩

theorem residual_unitBits (D : Matrix (Fin r) (Fin n) ℚ) (B : ℕ)
    (hB : ∀ i j, ratBits (D i j) ≤ B) (i j : Fin n) :
    ratBits ((1-rowGramProjector D) i j) ≤ residualEntryBits r n B := by
  have hval := computeGramProjector_bits D hB i j
  rw [computeGramProjector_eq] at hval
  have hid : ratBits ((1 : Matrix (Fin n) (Fin n) ℚ) i j) ≤ 3 := by
    rw [Matrix.one_apply]; split <;> decide
  exact (PrimalDual.ratBits_sub_le _ _).trans (by unfold residualEntryBits; omega)

end ResidualBitsCommon
end Geometry
end LinearProgramming
end Optimization
end OAI
