import OAI.Geometry.Hirsch.Law

noncomputable section

open Classical Filter
open scoped Topology

namespace OAI.Geometry.Hirsch.Layer.Law

variable {Ω : Type} [Fintype Ω] (p : Law Ω) (c : ℕ)

def Hits (h : ℕ) (sample : Fin ((2*c)^h) → Fin h → Ω) : Prop :=
  ∀ P : Fin h → Set Ω, (∀ i, (c : ℝ)⁻¹ ≤ p.prob (· ∈ P i)) → ∃ j, ∀ i, sample j i ∈ P i

theorem many_samples (hc : 0 < c) :
    ∀ᶠ h : ℕ in atTop, ∃ sample, p.Hits c h sample := by
  have ht : Tendsto (fun h : ℕ => (h : ℝ) / (2 : ℝ)^h * Fintype.card Ω) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt 1 (r := 2) (by norm_num)).mul_const
      (Fintype.card Ω : ℝ)
  filter_upwards [ht.eventually (eventually_lt_nhds zero_lt_one)] with h hh
  let I := {P : Fin h → Set Ω // ∀ i, (c : ℝ)⁻¹ ≤ p.prob (· ∈ P i)}
  let event := fun (P : I) (x : Fin h → Ω) => ∀ i, x i ∈ P.val i
  have he : ∀ P, (c : ℝ)⁻¹^h ≤ (p.copies h).prob (event P) := by
    intro P
    change _ ≤ (product _).prob (fun x => ∀ i, x i ∈ P.val i)
    rw [independent (fun _ : Fin h => p) (fun i x => x ∈ P.val i)]
    simpa using Finset.prod_le_prod₀ (s := Finset.univ) (fun _ _ => by positivity : ∀ i : Fin h,
      i ∈ Finset.univ → 0 ≤ (c : ℝ)⁻¹) (fun i _ => P.property i)
  have hn : Fintype.card I ≤ 2^(Fintype.card Ω*h) := by
    simpa [I,pow_mul] using Fintype.card_subtype_le (fun P : Fin h → Set Ω =>
      ∀ i, (c : ℝ)⁻¹ ≤ p.prob (· ∈ P i))
  have hpow : (Fintype.card Ω*h : ℕ) < (2 : ℝ)^h := by
    rw [div_mul_eq_mul_div,div_lt_one (by positivity)] at hh
    simpa [mul_comm] using hh
  have hmul : -(((2*c)^h : ℕ) : ℝ) * (c : ℝ)⁻¹^h = -(2 : ℝ)^h := by
    have hn : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    simp [neg_mul,mul_pow,hn]
  have hcnt : Fintype.card I * Real.exp (-(((2*c)^h : ℕ) : ℝ) * (c : ℝ)⁻¹^h) < 1 := by
    rw [hmul,Real.exp_neg,← div_eq_mul_inv,div_lt_one (Real.exp_pos _)]
    apply lt_of_le_of_lt _ (Real.exp_lt_exp.mpr hpow)
    calc
      _ ≤ (2 : ℝ)^(Fintype.card Ω*h) := by exact_mod_cast hn
      _ ≤ (Real.exp 1)^(Fintype.card Ω*h) := by gcongr; linarith [Real.add_one_le_exp 1]
      _ = _ := by rw [← Real.exp_nat_mul,mul_one]
  obtain ⟨sample,hs⟩ := (p.copies h).hitting ((2*c)^h) event _ he hcnt
  exact ⟨sample,fun P hp => hs ⟨P,hp⟩⟩

end OAI.Geometry.Hirsch.Layer.Law
