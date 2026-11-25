import OAI.Hierarchy.CollapseOracle
import OAI.Hierarchy.DescentPrivateDonorBillNumbers

namespace OAI
/-! # A dyadic internal host budget for the original open-network descent -/
namespace Hierarchy.CollapseOracle
open Catalyst CatalystSubstitution CorrectionBatch DescentCompiler.TerminalScale Filter
open scoped Classical BigOperators
noncomputable section

/-- The compiler's site budget and every subsequent host extension can be dyadic.
Its oracle still ranges over every implementation of the original tagged call. -/
def DyadicOpenNetworks (F : Type*) [Field F] (a C : ℝ) : Prop :=
  ∀ᶠ h : ℕ in atTop,
    ∀ j : ℕ, 2^h≤(2:ℕ)^j → (2:ℕ)^j≤(2^h)^2 → ∀ {k p : ℕ} (X : Approximation F k p),
    10*(X.size+1)≤2^j → ∃ d t : ℕ, 0<d ∧
      Real.logb 2 d ≤ C*(Real.logb 2 (2*(h:ℝ)))^2 ∧
      ∀ Y : Approximation F k (Tagged.pins h h),
      let os := List.replicate t (tagCall h Y)
      ∃ H : Host F k (d*p) (Sockets os),
        Agrees (independentCopies d X) (tableApprox H.width (exactValue os H)) ∧
          (hostSize H : ℝ) ≤ C*d*((((2:ℕ)^j:ℕ):ℝ)/(h:ℝ)^a + Fintype.card (Port p X.width))

theorem dyadic_site_budget {h M : ℕ} (low : 2^h≤M) (high : M≤(2^h)^2) :
    M≤hostRows M ∧ hostRows M≤2*M ∧ 2^h≤hostRows M ∧ hostRows M≤(2^h)^2 :=by
  have live : 0<M:=(Nat.two_pow_pos h).trans_le low
  refine ⟨hostPad _,hostRows_double live,low.trans (hostPad _),?_⟩
  rw [←pow_mul] at high ⊢
  exact Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow high)

theorem open_networks_from_dyadic {F : Type*} [Field F] {a C : ℝ} (cost : 0≤C)
    (compiled : DyadicOpenNetworks F a C) : OpenNetworks F a (2*C) :=by
  filter_upwards [compiled] with h build
  intro M lo hi k p X budget
  obtain ⟨cover,price,low,high⟩:=dyadic_site_budget lo hi
  obtain ⟨d,t,positive,copyLimit,make⟩:=build (Nat.clog 2 M) low high X (budget.trans cover)
  refine ⟨d,t,positive,copyLimit.trans (mul_le_mul_of_nonneg_right (by linarith : C≤2*C) (sq_nonneg _)),?_⟩
  intro Y
  obtain ⟨H,agrees,paid⟩:=make Y
  refine ⟨H,agrees,paid.trans ?_⟩
  let ports:=Fintype.card (Port p X.width)
  have doubled : ((hostRows M:ℕ):ℝ)≤2*(M:ℝ):=by exact_mod_cast price
  have denominator : 0≤(h:ℝ)^a:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have given:=div_le_div_of_nonneg_right doubled denominator
  have enough : ((hostRows M:ℕ):ℝ)/(h:ℝ)^a+(ports:ℝ)≤2*((M:ℝ)/(h:ℝ)^a+(ports:ℝ)):=by
    rw [mul_div_assoc] at given
    linarith only [given,(Nat.cast_nonneg ports : (0:ℝ)≤ports)]
  have scaled:=mul_le_mul_of_nonneg_left enough (mul_nonneg cost (Nat.cast_nonneg d))
  change C*(d:ℝ)*(((hostRows M:ℕ):ℝ)/(h:ℝ)^a+(ports:ℝ))≤2*C*d*((M:ℝ)/(h:ℝ)^a+(ports:ℝ))
  linarith only [scaled]

theorem descent_of_dyadic_open_networks {F : Type*} [Field F] {a C : ℝ} (small : 0<a)
    (gain : a<1) (positive : 0<C) (compiled : DyadicOpenNetworks F a C) : Descent F :=
  ⟨a,2*C,small,gain,by positivity,open_networks_from_dyadic positive.le compiled⟩

end
end Hierarchy.CollapseOracle

end OAI
