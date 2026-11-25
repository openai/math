import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic

/-! # Signed power coordinates on a prime axis

For a prime `p ≡ 3 (mod 4)`, the squares have order `(p-1)/2`. Their negatives
are the other coset. Indexing both cosets by the same powers pairs each unit
with its negative at the same position.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

/-- A generator of the square subgroup together with the two signed power lists. -/
structure PrimeAxisCosets (p : ℕ) where
  generator : (ZMod p)ˣ
  order_generator : orderOf generator = (p-1)/2
  equiv : Bool × Fin ((p-1)/2) ≃ (ZMod p)ˣ
  equiv_false (t : Fin ((p-1)/2)) : equiv (false, t) = generator ^ t.val
  equiv_true (t : Fin ((p-1)/2)) : equiv (true, t) = -(generator ^ t.val)
  isSquare_equiv_iff (z : Bool × Fin ((p-1)/2)) : IsSquare (equiv z) ↔ z.1 = false

namespace PrimeAxisCosets

private theorem not_isSquare_neg_unit {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    {u : (ZMod p)ˣ} (hu : IsSquare u) : ¬ IsSquare (-u) := by
  obtain ⟨v, rfl⟩ := hu.exists_sq
  rintro ⟨w, hw⟩
  have he : (w : ZMod p)^2 = -(v : ZMod p)^2 := by
    simpa only [pow_two, Units.val_neg, Units.val_mul] using congrArg Units.val hw.symm
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' v.ne_zero he hp

/-- Squaring a primitive unit gives the generator, and the sign separates its two cosets. -/
noncomputable def ofPrime (p : ℕ) [hprime : Fact p.Prime] (hp : p % 4 = 3) : PrimeAxisCosets p := by
  classical
  let m := (p-1)/2
  have hc : Fintype.card (ZMod p)ˣ = p-1 := (Nat.prime_iff_card_units p).mp hprime.out
  let a := (IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)).choose
  have ha : orderOf a = Nat.card (ZMod p)ˣ := IsCyclic.exists_ofOrder_eq_natCard.choose_spec
  rw [Nat.card_eq_fintype_card, hc] at ha
  let g := a^2
  have hg : orderOf g = m := by
    change orderOf (a^2) = (p-1)/2
    rw [orderOf_pow_of_dvd (by decide : 2 ≠ 0) (by rw [ha]; exact ⟨m, by dsimp [m]; omega⟩), ha]
  have hs (i : Fin m) : IsSquare (g ^ i.val) := (IsSquare.sq a).pow i.val
  have hi : Function.Injective (fun i : Fin m => g ^ i.val) := by
    intro i j hij
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (show i.val < orderOf g by rw [hg]; exact i.isLt)
      (show j.val < orderOf g by rw [hg]; exact j.isLt) hij
  let f : Bool × Fin m → (ZMod p)ˣ
    | (false, i) => g ^ i.val
    | (true, i) => -(g ^ i.val)
  have hsign (z : Bool × Fin m) : IsSquare (f z) ↔ z.1 = false := by
    rcases z with ⟨b, i⟩
    cases b
    · exact iff_of_true (hs i) rfl
    · exact iff_of_false (not_isSquare_neg_unit hp (hs i)) (by change true ≠ false; decide)
  have hf : Function.Injective f := by
    rintro ⟨b,i⟩ ⟨c,j⟩ h
    have hbc : b = false ↔ c = false := (hsign (b,i)).symm.trans (h ▸ hsign (c,j))
    have : b = c := by cases b <;> cases c <;> simp_all
    subst c
    apply congrArg (Prod.mk b)
    cases b
    · exact hi h
    · exact hi (neg_inj.mp h)
  have hcard : Fintype.card (Bool × Fin m) = Fintype.card (ZMod p)ˣ := by
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, hc, m]
    omega
  let e := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩)
  exact ⟨g, hg, e, fun _ => rfl, fun _ => rfl, hsign⟩

/-- The sign tests whether the corresponding residue is a square in the prime field. -/
theorem isSquare_coe_equiv_iff {p : ℕ} [Fact p.Prime] (C : PrimeAxisCosets p)
    (z : Bool × Fin ((p-1)/2)) : IsSquare ((C.equiv z : (ZMod p)ˣ) : ZMod p) ↔ z.1 = false := by
  rw [← C.isSquare_equiv_iff z]
  refine ⟨?_, fun h => h.map (Units.coeHom _)⟩
  rintro ⟨a, ha⟩
  have h : a ≠ 0 := by
    intro hzero
    simp [hzero] at ha
  refine ⟨Units.mk0 a h, Units.ext ?_⟩
  exact ha

end PrimeAxisCosets

end FiniteFourier
end LinearAlgebra
end OAI
