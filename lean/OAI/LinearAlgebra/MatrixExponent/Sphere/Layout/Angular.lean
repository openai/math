import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Squares

/-!
# Summing widths at cells and throughout the surface

The many untouched auxiliaries use their individual level bounds.
Charge all other residues by the private-species estimate, and use
the global number of collectors for the remaining legs.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing.Geo.Raw
open Classical Finset Rounds Real Packing
open SphereScale (Scales size budget probes q)

variable {F U X E V K : Type} [Fintype E] [Fintype V] {M r t : ℕ}
  {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} {h D T R g k ℓ L B m : ℕ} {W : ℝ} {P : Input F a b h D T R g W}
  {G : S.Geo P k} {e : E → ℕ} {thin : Place C → Prop} {selector : K → Prop}
  (hr : G.Raw ℓ L B m e thin selector) (s : Scales g ℓ D T L B m)
  (ha : M * r = m * B) (hb : M * t = m) (hM : M = SphereScale.chunks ℓ D)

include hr s ha hM in
private theorem seam_load (v : V) :
    push S.src (seamWidth C e) v + push S.dst (seamWidth C e) v ≤ 5 * (budget g : ℝ) ^ 2 * D * T := by
  let c := 5 * (budget g : ℝ) * D * T
  have hc : 0 ≤ c := by unfold c; positivity
  calc
    _ ≤ (S.seamDegree v : ℝ) * c := by
      simp only [push, seamDegree, Packing.degree_sum, Packing.arityCost,
        ← sum_add_distrib, Nat.cast_sum, sum_mul, Nat.cast_add, add_mul, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul]
      apply sum_le_sum
      intro i _
      have hh : seamWidth C e i ≤ c := hr.seam_le s ha hM i
      split_ifs <;> linarith only [hh]
    _ ≤ budget g * c := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hr.seams v)) hc
    _ = _ := by unfold c; ring

include hr s ha hb hM

private theorem site_load (v : V) (f : Place C → ℝ) (hf : ∀ i, f i ≤ legWidth C i)
    (A : ℝ) (hA : 0 ≤ A) (h : ∀ i, ¬thin i → f i ≤ A) :
    ∑ j, f ⟨v, j⟩ ≤ (budget g : ℝ) ^ 2 * D * T + (D : ℝ) ^ 5 * A := by
  have h₁ := hr.station_sum v (10 * (budget g : ℝ) * ((m : ℝ) * B)) A (by positivity) hA f
    (fun i hi => (hf i).trans (hr.thin_le s ha hb hM i hi)) h
  refine h₁.trans (add_le_add_left ?_ _)
  have hlarge : 16000 ≤ (budget g : ℝ) := by
    exact_mod_cast (show 16000 ≤ budget g by have := SphereScale.budget_large g; omega)
  calc
    _ = 16000 * (budget g : ℝ) * D * ((m : ℝ) * B * size ℓ D) := by unfold probes; push_cast; ring
    _ ≤ (budget g : ℝ) * budget g * D * T := by gcongr; exact_mod_cast s.lower
    _ = _ := by ring

theorem total_load : (∑ i, legWidth C i) + (∑ j, seamWidth C e j) ≤ 17 * (budget g : ℝ) ^ 2 * W := by
  have hW : 0 ≤ W := le_trans (by positivity) hr.occupied
  have sum_cell (f : V → ℝ) (A : ℝ) (hA : 0 ≤ A) (hf : ∀ v, f v ≤ A * D * T) :
      ∑ v, f v ≤ A * W := by
    have he := sum_le_card_nsmul univ f _ (fun i _ => hf i)
    simp only [card_univ, nsmul_eq_mul] at he
    linarith only [he, mul_le_mul_of_nonneg_left hr.occupied hA]
  have hseam : ∑ j, seamWidth C e j ≤ 5 * (budget g : ℝ) ^ 2 * W := by
    rw [← sum_push S.src]
    apply sum_cell _ _ (by positivity)
    intro v
    exact (le_add_of_nonneg_right (push_nonneg S.dst _ (fun _ => proxy_nonneg ..) _)).trans
      (hr.seam_load s ha hM v)
  let f (i : Place C) := if G.frozen i then 0 else legWidth C i
  have hmob : ∑ i, f i ≤ 2 * (budget g : ℝ) ^ 2 * W := by
    rw [Fintype.sum_sigma]
    apply sum_cell _ _ (by positivity)
    intro v
    have hf (i : Place C) : f i ≤ legWidth C i := by
      unfold f
      split_ifs <;> first | exact legWidth_nonneg .. | rfl
    have hh := hr.site_load s ha hb hM v f hf ((D : ℝ) ^ 3 * (T / (q ℓ D : ℝ))) (by positivity)
      (fun i _ => by unfold f; split_ifs with hi; positivity; exact hr.residue_le s ha hb hM i hi)
    have he : (D : ℝ) ^ 5 * ((D : ℝ) ^ 3 * (T / (q ℓ D : ℝ))) ≤ T := by
      rw [← mul_assoc, ← pow_add]
      exact (room s.Dpos (by decide)).trans
        (div_le_self (by positivity) (one_le_pow₀ (by exact_mod_cast s.Dpos)))
    have hp : 1 ≤ (budget g : ℝ) ^ 2 * D := by
      have : 1 ≤ budget g ^ 2 * D :=
        Nat.mul_pos (pow_pos (by have := SphereScale.budget_large g; omega) _) s.Dpos
      exact_mod_cast this
    linarith only [hh, he, mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg T)]
  have hfix : ∑ i : {i // G.frozen i}, legWidth C i.val ≤ 10 * (budget g : ℝ) ^ 2 * W := by
    have hh := sum_le_card_nsmul univ _ _ (fun (i : {i // G.frozen i}) _ => hr.leg_le s ha hb hM i.val)
    simp only [card_univ, nsmul_eq_mul] at hh
    linarith only [hh, mul_le_mul_of_nonneg_left hr.collectors (Nat.cast_nonneg (budget g))]
  have hsplit : (∑ i, legWidth C i) = ∑ i : {i // G.frozen i}, legWidth C i.val + ∑ i, f i := by
    rw [← sum_subtype (univ.filter G.frozen) (by simp) (legWidth C), sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    unfold f
    split_ifs <;> simp
  linarith only [hsplit, hmob, hfix, hseam]

variable [Field F] [Fintype K]

theorem chamber_load (v : V) : S.backdrop.chamberLoad e v ≤ T / (D : ℝ) ^ (ℓ + 2) * sqrt M := by
  have hs := hr.seam_load s ha hM v
  have hl := hr.site_load s ha hb hM v (legWidth C) (fun _ => le_rfl)
    (10 * (budget g : ℝ) * D * T) (by positivity) (fun i _ => hr.leg_le s ha hb hM i)
  have hD : 16 ≤ (D : ℝ) := by exact_mod_cast (show 16 ≤ D by have := s.bound; omega)
  have hD' : 1 ≤ (D : ℝ) := by linarith
  have hg : (budget g : ℝ) ≤ D := by exact_mod_cast (show budget g ≤ D by have := s.large; omega)
  have hs' : S.backdrop.chamberLoad e v ≤ 6 * (budget g : ℝ) ^ 2 * D * T + (D : ℝ) ^ 5 * (10 * budget g * D * T) := by
    change push S.src _ v + push S.dst _ v + push Sigma.fst (legWidth C) v ≤ _
    rw [show push Sigma.fst (legWidth C) v = ∑ j, legWidth C ⟨v, j⟩ from sum_place _ _]
    linarith only [hs, hl]
  have hm : sqrt (M : ℝ) = q ℓ D := by
    rw [hM, SphereScale.chunks, Nat.cast_pow, sqrt_sq (by positivity)]
  calc
    _ ≤ _ := hs'
    _ ≤ 6 * (D : ℝ) ^ 2 * D * T + (D : ℝ) ^ 5 * (10 * D * D * T) := by gcongr
    _ ≤ 16 * (D : ℝ) ^ 7 * T := by
      linarith only [mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD' (by decide : 3 ≤ 7))
        (Nat.cast_nonneg T)]
    _ ≤ (D : ℝ) ^ 8 * T := by rw [pow_succ' (D : ℝ) 7]; gcongr
    _ ≤ _ := by
      rw [hm, div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm ((D : ℝ) ^ 8),
        mul_assoc, ← pow_add, q, Nat.cast_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD' (by omega)) (by positivity)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing.Geo.Raw
