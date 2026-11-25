import OAI.Hierarchy.DescentStackScale
import OAI.Hierarchy.CollapseOracle

namespace OAI
/-! # From the integral terminal host tariff to the power saving for an open network -/

namespace Hierarchy.DescentCompiler
open Catalyst CatalystSubstitution CorrectionBatch CollapseOracle

theorem open_host_exponent (B : ℕ) (pos : 0<B) :
    0 < 1/(2*(B:ℝ)) ∧ 1/(2*(B:ℝ)) < 1 := by
  have hb : 1≤B := pos
  have one : (1:ℝ)≤B := by exact_mod_cast hb
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity)).mpr
    linarith

/-- The last dyadic rounding loses a factor of two. All exterior incidences
retain a constant price even when the tagged host has many exterior pins. -/
theorem open_host_rate (B h C d M e z : ℕ) (pos : 0<B) (hh : 0<h)
    (packed : z*2^(Nat.log 2 h/(2*B))≤C*d*(M+2^(Nat.log 2 h/(2*B))*e)) :
    (z:ℝ) ≤ (2*(C:ℝ))*d*((M:ℝ)/(h:ℝ)^(1/(2*(B:ℝ)))+e) := by
  let T : ℝ := (2:ℝ)^(Nat.log 2 h/(2*B))
  let Q : ℝ := (h:ℝ)^(1/(2*(B:ℝ)))
  have ht : 0<T := by dsimp [T];positivity
  have hq : 0<Q := by dsimp [Q];positivity
  have gain : Q≤2*T := by
    simpa only [Q,T,Nat.cast_mul,Nat.cast_ofNat] using age_saving h (2*B) hh (by omega)
  have money : (z:ℝ)*T ≤ (C:ℝ)*d*((M:ℝ)+T*e) := by dsimp [T];exact_mod_cast packed
  have saved : (M:ℝ)/T ≤ (2*M)/Q := by
    apply (div_le_div_iff₀ ht hq).mpr
    nlinarith only [mul_le_mul_of_nonneg_left gain (Nat.cast_nonneg (α:=ℝ) M)]
  change (z:ℝ) ≤ (2*(C:ℝ))*d*((M:ℝ)/Q+e)
  calc
    _ ≤ (C:ℝ)*d*((M:ℝ)+T*e)/T := (le_div_iff₀ ht).mpr money
    _ = (C:ℝ)*d*((M:ℝ)/T+e) := by field_simp
    _ ≤ (C:ℝ)*d*((2*M)/Q+e) :=
      mul_le_mul_of_nonneg_left (add_le_add saved le_rfl) (by positivity)
    _ ≤ _ := by
      rw [mul_div_assoc]
      nlinarith only [show 0≤(C:ℝ)*d*e by positivity]

/-- The price of one concrete compiled host is preserved when that host is
relabelled with any physical implementation of its tagged calls. In particular
the copy count and the number of calls precede the choice of implementation. -/
theorem open_host_all_replacements {F : Type*} [Field F] {k p : ℕ}
    (X : Approximation F k p) (B h C d M t : ℕ) (pos : 0<B) (hh : 0<h)
    (Y : Approximation F k (Tagged.pins h h))
    (H : Host F k (d*p) (Sockets (List.replicate t (tagCall h Y))))
    (same : Agrees (independentCopies d X)
      (tableApprox H.width (exactValue (List.replicate t (tagCall h Y)) H)))
    (packed : hostSize H*2^(Nat.log 2 h/(2*B)) ≤
      C*d*(M+2^(Nat.log 2 h/(2*B))*Fintype.card (Port p X.width))) :
    ∀ Z : Approximation F k (Tagged.pins h h),
      let os := List.replicate t (tagCall h Z)
      ∃ H' : Host F k (d*p) (Sockets os),
        Agrees (independentCopies d X) (tableApprox H'.width (exactValue os H')) ∧
        (hostSize H' : ℝ) ≤ (2*(C:ℝ))*d*
          ((M:ℝ)/(h:ℝ)^(1/(2*(B:ℝ)))+Fintype.card (Port p X.width)) := by
  intro Z os
  obtain ⟨agree,price⟩:=retag_host h t Y Z (independentCopies d X) H same
  refine ⟨retag h t Y Z H,agree,?_⟩
  rw [price]
  exact open_host_rate B h C d M _ _ pos hh packed

end Hierarchy.DescentCompiler

end OAI
