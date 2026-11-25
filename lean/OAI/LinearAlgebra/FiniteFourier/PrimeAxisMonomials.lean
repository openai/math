import OAI.LinearAlgebra.FiniteFourier.QuadraticPeriods

/-! # The positive-power basis of a prime cyclotomic quotient

Multiplying the monic power basis by the unit `X` changes its exponents
from `0,…,p-2` to `1,…,p-1`, the nonzero residue classes modulo `p`.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Module Polynomial

variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime]

/-- Ascending enumeration of the nonzero residue classes modulo a prime. -/
def primeAxisResidueIndex : Fin (p-1) ≃ (ZMod p)ˣ where
  toFun i := Units.mk0 (((i.val+1 : ℕ) : ZMod p)) (by
    have hi : i.val+1 < p := by have := i.isLt; omega
    exact (ZMod.val_ne_zero _).mp (by rw [ZMod.val_natCast_of_lt hi]; omega))
  invFun a := ⟨(a : ZMod p).val - 1, by
    have := (a : ZMod p).val_lt
    have := (ZMod.val_ne_zero _).mpr a.ne_zero
    omega⟩
  left_inv i := by
    apply Fin.ext
    change (((i.val+1:ℕ) : ZMod p)).val - 1 = i.val
    rw [ZMod.val_natCast_of_lt (by have := i.isLt; omega)]
    omega
  right_inv a := by
    apply Units.ext
    change (((a : ZMod p).val - 1 + 1 : ℕ) : ZMod p) = a
    have ha := (ZMod.val_ne_zero _).mpr a.ne_zero
    rw [Nat.sub_add_cancel (by omega), ZMod.natCast_zmod_val]

/-- The monomials indexed by nonzero residues give a basis of the universal
prime cyclotomic quotient, over any commutative coefficient ring. -/
theorem exists_primeAxisResidueBasis :
    ∃ b : Basis (ZMod p)ˣ R (AdjoinRoot (cyclotomic p R)),
      ∀ a, b a = primeAxisCharacter R p (a : ZMod p) := by
  cases subsingleton_or_nontrivial R with
  | inl h =>
    let := h
    let := Module.subsingleton R (AdjoinRoot (cyclotomic p R))
    exact ⟨Basis.ofEquivFun (LinearEquiv.ofSubsingleton _ _), fun a => Subsingleton.elim _ _⟩
  | inr h =>
    let := h
    let b := AdjoinRoot.powerBasis' (cyclotomic.monic p R)
    have hd : b.dim = p-1 := (natDegree_cyclotomic p R).trans (Nat.totient_prime Fact.out)
    let e := (finCongr hd).trans (primeAxisResidueIndex p)
    let X₀ := AdjoinRoot.root (cyclotomic p R)
    have hx : IsUnit X₀ :=
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, (Fact.out : Nat.Prime p).pos, primeAxis_pow R p⟩).isUnit
    let b' := (b.basis.map (hx.unit.mulLeftLinearEquiv R _)).reindex e
    refine ⟨b', fun a => ?_⟩
    have ha := (ZMod.val_ne_zero _).mpr a.ne_zero
    simp only [b', Basis.reindex_apply, Basis.map_apply, Units.mulLeftLinearEquiv_apply,
      hx.unit_spec, b.basis_eq_pow, primeAxisCharacter, AddChar.zmodChar_apply]
    change X₀ * X₀ ^ ((a : ZMod p).val - 1) = X₀ ^ (a : ZMod p).val
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]

/-- The action of the cyclic address group on the class of `X` supplies the
value of each basis vector as an explicit monomial. -/
def primeAxisResidueBasis : Basis (ZMod p)ˣ R (AdjoinRoot (cyclotomic p R)) :=
  Classical.choose (exists_primeAxisResidueBasis R p)

theorem primeAxisResidueBasis_apply (a : (ZMod p)ˣ) :
    primeAxisResidueBasis R p a = primeAxisCharacter R p (a : ZMod p) :=
  Classical.choose_spec (exists_primeAxisResidueBasis R p) a

end

end

end FiniteFourier
end LinearAlgebra
end OAI
