import OAI.Hierarchy.TaggedWireTurnShelf
import OAI.Hierarchy.TaggedWideSiteCost
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Uniform ordinary work for the complete fixed binary turn and port shelf -/
namespace Hierarchy.WireTelescope.TurnShelf
open Filter Real
open scoped BigOperators

/-- A positive cap is rounded to the next dyadic word boundary, with a
strictly representable end address and at most twice the true width. -/
def exponent (v : ℕ) := Nat.log 2 v+1

theorem dyadic_room (v : ℕ) (positive : 0<v) :
    v<2^exponent v ∧ 2^exponent v≤2*v := by
  refine ⟨Nat.lt_pow_succ_log_self (by decide) _,?_⟩
  rw [exponent,pow_succ,Nat.mul_comm 2 v]
  exact Nat.mul_le_mul_right 2 (Nat.pow_log_le_self _ positive.ne')

/-- Price all finite paid sites and immutable local turn slots simultaneously.
Here K is the exact local port cap multiplier from the terminal cash ledger.
The reference and height of the controlled word selectors are charged. -/
theorem work_bound (F : Type*) [Field F] (A : ℝ) (slots roles K B : ℕ)
    (hK : 0<K) (_hR : 0<roles) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ h : ℕ in atTop,∀ w sites : ℕ,0<w→(w:ℝ)≤(h:ℝ)^A→sites≤B*2^h→
      let N:=network F slots (exponent roles) (exponent (K*w))
      ((sites*(N.cells+N.internal):ℕ):ℝ)≤C*((2:ℝ)^h*w*log (h:ℝ)) := by
  let c := max 1 (logb 2 (K:ℝ)+2+A/log 2)
  let P := exponent roles
  let D := (B*slots*2308*(2^P)*(2*K):ℕ)
  refine ⟨(D:ℝ)*(c+(P:ℝ)+1)+1,by have hc : 1≤c:=le_max_left ..;positivity,?_⟩
  filter_upwards [(Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1,
    eventually_ge_atTop (1:ℕ)] with h hl hh
  change 1≤log (h:ℝ) at hl
  intro w sites hw wcap count N
  have kw := Nat.mul_pos hK hw
  have widthBound := (dyadic_room (K*w) kw).2
  have logs := Tagged.site_log A K hK h w (K*w) hl hh hw wcap kw le_rfl
  have logpos := (zero_le_one (α:=ℝ)).trans hl
  have cBound := mul_le_mul_of_nonneg_right (le_max_right 1 (logb 2 (K:ℝ)+2+A/log 2)) logpos
  have const : (P:ℝ)+1≤((P:ℝ)+1)*log (h:ℝ) :=
    le_mul_of_one_le_right (by positivity) hl
  have depth : ((exponent (K*w)+P+2:ℕ):ℝ)≤(c+(P:ℝ)+1)*log (h:ℝ) := by
    push_cast [exponent]
    dsimp only [c]
    linarith [logs,cBound,const]
  have raw := Nat.mul_le_mul count (size F slots P (exponent (K*w)))
  have compressed :
      sites*(N.cells+N.internal)≤D*2^h*w*(exponent (K*w)+P+2) := by
    refine raw.trans ?_
    unfold width
    calc
      _ ≤ B*2^h*(slots*(2308*(2^P*(2*(K*w)))*(exponent (K*w)+P+2))) := by gcongr
      _ = _ := by dsimp only [D];ring
  have realBill : ((sites*(N.cells+N.internal):ℕ):ℝ) ≤ (D:ℝ)*2^h*w*(exponent (K*w)+P+2:ℕ) := by
    exact_mod_cast compressed
  calc
    _ ≤ _ := realBill
    _ ≤ (D:ℝ)*2^h*w*((c+(P:ℝ)+1)*log (h:ℝ)) := by gcongr
    _ ≤ _ := by
      have h0 : 0≤(2:ℝ)^h*w*log (h:ℝ) := mul_nonneg (by positivity) logpos
      nlinarith only [h0]

end Hierarchy.WireTelescope.TurnShelf

end OAI
