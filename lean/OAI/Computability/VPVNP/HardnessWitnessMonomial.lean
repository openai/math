import OAI.Computability.VPVNP.Classes

/-! # Specializing the selected monomials at a Boolean witness

A selected scalar may be labelled by one output variable or one witness variable.
After specialization, a selected witness label contributes zero if its bit is false
and one if it is true. The output-variable labels survive as formal variables.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HardnessWitness

open scoped Classical
open MvPolynomial

/-- A scalar, optionally multiplied by one labelled variable. -/
noncomputable def monomial {F V : Type*} [Field F] (a : F) (t : Option V) :
    MvPolynomial V F := C a * t.elim 1 X

/-- The formal variable retained by a compatible label, or the constant one. -/
def variableWeight {F X W : Type*} [Field F] : Option (X ⊕ W) → X ⊕ F
  | some (.inl v) => .inl v
  | some (.inr _) | none => .inr 1

private theorem witnessValue_monomial {F : Type*} [Field F] {X W : Type}
    (a : F) (t : Option (X ⊕ W)) (y : W → Bool)
    (h : ∀ w, t = some (.inr w) → y w = true) :
    witnessValue y (monomial a t) = C a * (variableWeight (F := F) t).elim MvPolynomial.X C := by
  rcases t with _ | (v | w) <;> simp_all [monomial, witnessValue, variableWeight]

/-- A false selected witness variable annihilates the product. Otherwise the
product factors into the selected scalars and the selected output variables. -/
theorem witnessValue_prod_monomial {F : Type*} [Field F] {X W : Type} {k : ℕ}
    (a : Fin k → F) (tag : Fin k → Option (X ⊕ W)) (x : Fin k → Bool) (y : W → Bool) :
    witnessValue y (∏ i, if x i then monomial (a i) (tag i) else 1) =
      if (∀ i w, x i = true → tag i = some (.inr w) → y w = true) then
        (∏ i, if x i then C (a i) else 1) *
          (∏ i, if x i then (variableWeight (F := F) (tag i)).elim MvPolynomial.X C else 1)
      else 0 := by
  rw [map_prod]
  split_ifs with compatible
  · rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    cases hi : x i with
    | false => simp
    | true => simpa [hi] using witnessValue_monomial (a i) (tag i) y (fun w => compatible i w hi)
  · push Not at compatible
    obtain ⟨i, w, hi, ht, hw⟩ := compatible
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi, ht, hw, monomial, witnessValue]

end HardnessWitness

end VPVNP
end Computability
end OAI
