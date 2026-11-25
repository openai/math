import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementCatalogue
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementCircuit

/-! # The shared table circuit attached to a catalogue of actual record terms -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical BigOperators
namespace PortGraph.ShapeCatalogue

open UniformDecorations ReplacementTemplate ReplacementChoices Arithmetic.RecursiveBlock MvPolynomial

variable {F : Type} [Field F] {K n w c a : ℕ} {ε : ℝ}
  (C : ShapeCatalogue F K w c)

/-- The degree-four bound on each slot of a bounded patch gives a uniform
number of identifiers for the vertices of each replacement term. -/
theorem role_bound (j : C.Tag n ε) : Fintype.card (C.templates j).Role ≤ max 1 (4*K) := by
  let R := j.1.val.shape
  apply (C.selected j).roles_le.trans
  apply max_le_max_left
  apply (Fintype.card_le_of_injective (fun s : R.Stub => s.val) Subtype.val_injective).trans
  change Fintype.card (Σ v, Fin (R.typeAt v).degree.val) ≤ 4*K
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∑ _ : Fin R.size.val, 4 :=
      Finset.sum_le_sum (fun v _ => Nat.le_of_lt_succ (R.typeAt v).degree.isLt)
    _ = 4 * R.size.val := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_of_lt_succ R.size.isLt)

abbrev listLength (r : Checked n K ε) := C.length r.val.shape r.property.connected

theorem listLength_le (r : Checked n K ε) : C.listLength r ≤ 2^(w+c) :=
  C.length_le _ _

/-- A single fixed-width code for every possible checked record, list index and role
at old cap `n`. Its data length uses one copy of the old width. -/
def encodeRole (n : ℕ) (hn : 0 < n) (ε : ℝ) :
    RoleLabel (C.templates (N := n) (ε := ε)) ↪
      Fin (2^(w+(recordExponent K+c+max 1 (4*K))*Nat.clog 2 (2*n))) :=
  roleCode C.templates (checked_role_card hn C.listLength C.listLength_le C.templates C.role_bound)

/-- The polynomial mass over these accepted decorated maps compiles to
one arithmetic circuit computing every entry of the smaller map's table. -/
theorem circuit (hn : 0 < n) (hw : 0 < w)
    (mass : Zpoly n w =
      ∑ q : ((C.rules n ε).acceptedFamily (C.encodeRole n hn ε) C.coefficient (max 1 (n/a))).Class,
        (C.rules n ε).acceptedWeight (C.encodeRole n hn ε) C.coefficient q) :
    let d := roundConstant K c (max 1 (4*K)) (PatchShape.entryExponent K)
    ∃ w', 0 < w' ∧ w' ≤ 10*w+d*Nat.clog 2 (2*n) ∧
      ∃ p : Family F (Address w) (Address w'), p.cost ≤ 2^(d*(w + Nat.clog 2 (2*n))) ∧
        Zpoly n w = bind₁ (familyPolynomial p) (Zpoly (max 1 (n/a)) w') :=
  circuit_of_role_classes hn hw C.listLength C.listLength_le C.templates C.role_bound
    (C.rules n ε) C.coefficient C.coefficient_hasFormula mass

end PortGraph.ShapeCatalogue

end

end SpectralBooks
end LinearAlgebra
end OAI
