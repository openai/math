import OAI.LinearAlgebra.SpectralBooks.UniformDecorations.GridRoundCircuit
import OAI.LinearAlgebra.SpectralBooks.PortGraph.CheckedRoleHeader

/-! # One arithmetic circuit for every output of a replacement round -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace PortGraph.ReplacementChoices

open UniformDecorations ReplacementTemplate PlanarPatch Arithmetic.RecursiveBlock MvPolynomial
open scoped Classical

/-- A uniform positive cutoff exists, also for the one-patch case where the
only compressed vertex is an isolated root. -/
theorem exists_positive_systems (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ, 0 < n → System n K ε := by
  obtain ⟨K, h⟩ := exists_systems ε hε
  let M := GridPin.rooted 0 0
  have hsize : Fintype.card (GridPin.Vertex 1 1) ≤ 5 := by rw [GridPin.vertex_count]
  obtain ⟨z, hz, _⟩ := (h 5 (by decide)).unique M hsize (GridPin.spherical 0 0)
  have hbound := ((h 5 (by decide)).partition_checks M z hz).2.1 M.root
  have hm : M.root ∈ RootedMap.patchFiber (fun x => MapLabels.patchName (z x)) M.root := by
    simp [RootedMap.patchFiber]
  exact ⟨K, (Finset.card_pos.mpr ⟨_,hm⟩).trans_le hbound.2, h⟩

/-- The constants used in the one-round gate/width bound depend only on
the patch cutoff, the straightening list overhead, the number of roles per
term, and the exponent bounding local table expressions. -/
def roundConstant (K c b B : ℕ) :=
  let A := recordExponent K+c+b
  49 + 4*(2*A+16) + A + B

/-- Compile the reconstructed map's local formulas once. The identity in
the hypothesis is the weighted sum over accepted decorated map classes.
It is converted into an exact polynomial identity after substituting the
compiled registers into the next universal polynomial. -/
theorem circuit_of_role_classes {F : Type*} [Field F] {K a n w c b B : ℕ} {ε : ℝ}
    (hn : 0 < n) (hw : 0 < w)
    (L : Checked n K ε → ℕ) (hL : ∀ r, L r ≤ 2^(w+c))
    (T : ((r : Checked n K ε) × Fin (L r)) → ReplacementTemplate.{0,0,0})
    [∀ j, Fintype (T j).Role] (hr : ∀ j, Fintype.card (T j).Role ≤ b)
    (R : LocalRules (I := ℕ) T)
    (value : (v : RoleLabel T) → (RolePort T v → Bits (8*w)) → MvPolynomial (Address w) F)
    (hform : ∀ v x, HasFormula (2^(B*(w+1))) (value v x))
    (identity : let code := roleCode T (checked_role_card hn L hL T hr)
      Zpoly n w = ∑ x : (R.acceptedFamily code value (max 1 (n/a))).Class,
        R.acceptedWeight code value x) :
    ∃ w' : ℕ, 0 < w' ∧ w' ≤ 10*w + roundConstant K c b B * Nat.clog 2 (2*n) ∧
      ∃ p : Family F (Address w) (Address w'), p.cost ≤ 2^(roundConstant K c b B*(w + Nat.clog 2 (2*n))) ∧
        Zpoly n w = bind₁ (familyPolynomial p) (Zpoly (max 1 (n/a)) w') := by
  let A := recordExponent K + c + b
  let code := roleCode T (checked_role_card hn L hL T hr)
  have heq := R.Z_eq_role_classes code value (max 1 (n/a))
  exact build_compression_round (A := A) (B := B) hn hw (R.spec code value) le_rfl le_rfl
    (R.tensor_hasFormula code (Nat.one_le_pow _ _ (by decide)) value hform) (identity.trans heq.symm)

end PortGraph.ReplacementChoices

end

end SpectralBooks
end LinearAlgebra
end OAI
