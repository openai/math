import OAI.Hierarchy.TaggedApproximation
import OAI.Hierarchy.TaggedExact
import OAI.ThreeFlat.BitNetwork.PinMap

namespace OAI
/-! # Initial feasible rates for the tagged predicate

An exact finite verifier gives a catalyst of width zero in every direction.
At positive address lengths the bitonic bill gives rate three at every width
exponent, and rate two whenever the payload is at least as wide as the address.
-/

noncomputable section
namespace Hierarchy.Tagged.Exact

open ThreeFlat
open Catalyst Filter
open scoped Classical

/-- Place an ordinary verifier at the origin of the catalyst frame. -/
def atOrigin {F : Type*} {p : ℕ} (k : ℕ) (N : BitNetwork F p) : Approximation F k p where
  width := fun _ => 0
  network := N.restrictPins fun i => some (Fintype.equivFin (Catalyst.Port p (fun _ : Fin k => 0)) (.inl i))

theorem size_atOrigin {F : Type*} [Field F] {p : ℕ} (k : ℕ) (N : BitNetwork F p) :
    (atOrigin k N).size = N.cells + N.internal + p := by
  let : IsEmpty (Wire (fun _ : Fin k => 0) × Bool) := ⟨fun j => Fin.elim0 j.1.2⟩
  let e := Equiv.sumEmpty (Fin p) (Wire (fun _ : Fin k => 0) × Bool)
  exact congrArg (fun q => N.cells + N.internal + q)
    ((Fintype.card_congr e).trans (Fintype.card_fin p))

private theorem coeff_atOrigin {F : Type*} [Field F] {p : ℕ} (k : ℕ) (N : BitNetwork F p)
    (x : Catalyst.Port p (fun _ : Fin k => 0) → Bool) :
    (atOrigin k N).coeff x = ideal (fun _ : Fin k => 0) N.eval x := by
  let e := Fintype.equivFin (Catalyst.Port p (fun _ : Fin k => 0))
  change (N.restrictPins (fun i => some (e (.inl i)))).eval (fun j => x (e.symm j)) = _
  rw [BitNetwork.restrictPins_eval]
  have through (j : Wire (fun _ : Fin k => 0)) : x (.inr (j,false)) = x (.inr (j,true)) :=
    Fin.elim0 j.2
  rw [ideal, ite_eq_left through]
  simp

theorem gap_atOrigin {F : Type*} [Field F] {p : ℕ} (k : ℕ) (N : BitNetwork F p)
    (D : ℝ) : (atOrigin k N).Gap N.eval D := by
  intro P
  left
  funext x
  exact sub_eq_zero.mpr (coeff_atOrigin k N x)

private theorem budget {h w d : ℕ} (hh : 1 ≤ h) (hw : w+h+1 ≤ 3*d) :
    8192*(w+h+1)*2^h*(h+1)^2 + pins h w ≤ 100000*2^h*d*h^2 := by
  have hs : (h+1)^2 ≤ 4*h^2 := by
    calc
      (h+1)^2 ≤ (2*h)^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  have ha : 8192*(w+h+1)*2^h*(h+1)^2 ≤ 8192*(3*d)*2^h*(4*h^2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hw)) hs
  have hp : pins h w ≤ 2^h*(6*d)*h^2 := calc
    _ = 2^h*(2*w+h) := by unfold pins; ring
    _ ≤ 2^h*(6*d) := Nat.mul_le_mul_left _ (by omega)
    _ ≤ 2^h*(6*d)*h^2 := Nat.le_mul_of_pos_right _ (Nat.pow_pos hh)
  calc
    _ ≤ 8192*(3*d)*2^h*(4*h^2) + 2^h*(6*d)*h^2 := Nat.add_le_add ha hp
    _ = 98310*(2^h*d*h^2) := by ring
    _ ≤ 100000*(2^h*d*h^2) := Nat.mul_le_mul_right _ (by decide)
    _ = _ := by ring

private theorem feasible_of_verifiers {F : Type*} [Field F] (k : ℕ) (a : ℝ) (r : ℕ)
    (N : (h : ℕ) → BitNetwork F (pins h (width h a)))
    (ev : ∀ h, (N h).eval = coeff F h (width h a))
    (hb : ∀ h, 1 ≤ h → (N h).cells + (N h).internal + pins h (width h a) ≤
      100000*2^h*(width h a)*h^r) : Feasible F k a r := by
  refine ⟨100000,1,by norm_num,by norm_num,?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
  refine ⟨atOrigin k (N h),?_,?_⟩
  · rw [size_atOrigin, work, Real.rpow_natCast]
    simp only [← mul_assoc]
    exact_mod_cast hb h hh
  · rw [← ev h]
    exact gap_atOrigin k _ _

/-- The sparse correction spacing pays the exact verifier bill using the open
data ports already counted in any approximation of this format. -/
theorem correction_budget (F : Type*) [Field F] {k h w : ℕ} (hh : 0 < h)
    (X : Approximation F k (pins h w)) :
    (typedNetwork F h w).cells + (typedNetwork F h w).internal ≤ 16384*(h+1)^2*X.size := by
  have hp : pins h w ≤ X.size := by
    simp [Approximation.size, Fintype.card_sum]
    omega
  have hw : w+h+1 ≤ 2*(2*w+h) := by omega
  calc
    _ ≤ 8192*(w+h+1)*2^h*(h+1)^2 := typedNetwork_size F h w
    _ = 8192*(h+1)^2*(2^h*(w+h+1)) := by ring
    _ ≤ 8192*(h+1)^2*(2^h*(2*(2*w+h))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hw)
    _ = 16384*(h+1)^2*pins h w := by unfold pins; ring
    _ ≤ _ := Nat.mul_le_mul_left _ hp

/-- At every real width exponent, cubic overhead already gives zero error. -/
theorem feasible_three (F : Type*) [Field F] (k : ℕ) (a : ℝ) : Feasible F k a 3 := by
  apply feasible_of_verifiers k a 3 (fun h => network F h (width h a))
    (fun h => funext (network_eval F h (width h a)))
  intro h hh
  let w := width h a
  have hpos : (0 : ℝ) < h := by exact_mod_cast (show 0 < h from hh)
  have hw : 0 < w := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hpos a)
  have hw' : w ≤ w*h := Nat.le_mul_of_pos_right _ hh
  have hh' : h ≤ w*h := Nat.le_mul_of_pos_left _ hw
  calc
    _ ≤ 8192*(w+h+1)*2^h*(h+1)^2 + pins h w :=
      Nat.add_le_add_right (network_size F h w) _
    _ ≤ 100000*2^h*(w*h)*h^2 := budget hh (by omega)
    _ = _ := by change _ = 100000*2^h*w*h^3; ring

/-- Payloads at least as wide as the address require only quadratic overhead. -/
theorem feasible_two (F : Type*) [Field F] (k : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    Feasible F k a 2 := by
  apply feasible_of_verifiers k a 2 (fun h => network F h (width h a))
    (fun h => funext (network_eval F h (width h a)))
  intro h hh
  let w := width h a
  have hr : (1:ℝ) ≤ h := by exact_mod_cast hh
  have hrw : (h:ℝ) ≤ (h:ℝ)^a := by
    simpa using Real.rpow_le_rpow_of_exponent_le hr ha
  have hw : h ≤ w := by
    change h ≤ ⌈(h:ℝ)^a⌉₊
    exact_mod_cast hrw.trans (Nat.le_ceil _)
  exact (Nat.add_le_add_right (network_size F h w) _).trans (budget hh (by omega))

theorem rates_nonempty (F : Type*) [Field F] (k : ℕ) (a : ℝ) : (rates F k a).Nonempty :=
  ⟨3,by norm_num,feasible_three F k a⟩


end Hierarchy.Tagged.Exact

end
end OAI
