import OAI.Hierarchy.TaggedPassBill
import OAI.Hierarchy.TaggedPassRun
import OAI.Hierarchy.TaggedRadixBatches
import OAI.Hierarchy.TaggedWidthLimit

namespace OAI
/-! # Feasibility of the installed stable radix construction at width h -/
noncomputable section
namespace Hierarchy.Tagged.Radix
open Catalyst Filter
open scoped Classical

/-- The concrete height/volume schedule and exact trivalent shells. The
constants may depend on the two fixed format exponents. -/
def Layout (F : Type*) [Field F] (k : ℕ) (a B : ℝ) : Prop :=
  ∃ d c K shell : ℕ, ∃ C : ℝ, 0<K ∧ 0<C ∧ ∀ᶠ h : ℕ in atTop,
    ∃ (n : ℕ) (g : ℕ → PassFormat), ((n+1:ℕ):ℝ) ≤ C*(h:ℝ)^(1-1/a) ∧
      (∀ i,FormatBounds a B h d c K (g i)) ∧
      ∀ Y : ∀ i,(g i).Calls F k, ∃ S : StageRun h n Y,S.Room shell

theorem feasible_of_stages {F : Type*} [Field F] {k : ℕ} {a B x y : ℝ}
    (ha : 1<a) (hB : 1<B) (hx : 0≤x) (hy : 0≤y) (f : Feasible F k a x)
    (p : Feasible F k B y) (layout : Layout F k a B) :
    Feasible F k 1 (1-1/a+max (x/a) y) := by
  obtain ⟨d,c,K,shell,C,hK,hC,stages⟩ := layout
  obtain ⟨A,U,D,hA,hU,hD,approx⟩ := priced_batches ha hB hx hy f p
    (K:=(K:ℝ)) (by exact_mod_cast hK) c d
  refine ⟨C*(2*(shell:ℝ)+2*A+U),D,by positivity,by linarith,?_⟩
  filter_upwards [stages,approx,eventually_ge_atTop (1:ℕ),
    GapScale.eventual_polynomial D (6*(k:ℝ)*C) 1 zero_le_one] with h shape build hh spend
  obtain ⟨n,g,count,bounds,realize⟩ := shape
  have ready (i : ℕ) : ∃ Y : (g i).Calls F k,Y.Paid (A*work h h (x/a)) (U*work h h y) (2*gap D h) := by
    have b := bounds i
    have wide := b.widePayload.2
    rw [Nat.mul_assoc] at wide
    obtain ⟨X,Z,xc,xg,zc,zg⟩ := build _ _ _ _ _ b.firstLow b.firstHigh b.wideLow b.wideHigh
      (by exact_mod_cast b.firstMass) (by exact_mod_cast b.firstRoom) b.firstPayload.2 wide
    obtain ⟨Y,_,yc,yg,_,_⟩ := build _ _ _ _ _ b.secondLow b.secondHigh b.wideLow b.wideHigh
      (by exact_mod_cast b.secondMass) (by exact_mod_cast b.secondRoom) b.secondPayload.2 wide
    exact ⟨⟨X,Y,Z⟩,xc,yc,zc,xg,yg,zg⟩
  choose Y good using ready
  obtain ⟨S,room⟩ := realize Y
  obtain ⟨X,cost,score⟩ := S.install room (fun i _ => good i)
  have one : 1≤(h:ℝ) := by exact_mod_cast hh
  have cbound := count.trans (mul_le_mul_of_nonneg_left
    (show (h:ℝ)^(1-1/a) ≤ h by
      calc
        (h:ℝ)^(1-1/a) ≤ (h:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le one
          (sub_le_self _ (one_div_nonneg.mpr (by linarith)))
        _ = h := Real.rpow_one _) hC.le)
  rw [Real.rpow_one] at spend
  have fee : 2*(k:ℝ)*(3*((n+1:ℕ):ℝ)) ≤ gap D h := by
    have paid := mul_le_mul_of_nonneg_left cbound (show 0≤6*(k:ℝ) by positivity)
    nlinarith only [paid,spend,mul_nonneg (show 0≤6*(k:ℝ)*C by positivity) (Nat.cast_nonneg h)]
  rw [width_one]
  exact ⟨X,cost.trans (pass_bill hh ha hx hA hU hC count),
    Approximation.Gap.mono X score (by linarith)⟩

theorem radix_bound {F : Type*} [Field F] {k : ℕ}
    (layouts : ∀ {a B : ℝ},1<a → 1<B → Layout F k a B) : RadixBound F k :=
  fun ha hB hx hy f p => feasible_of_stages ha hB hx hy f p (layouts ha hB)

end Hierarchy.Tagged.Radix

end
end OAI
