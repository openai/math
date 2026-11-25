import OAI.Geometry.Hirsch.Palette

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

structure Law (Ω : Type) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

namespace Law

variable {Ω I : Type} [Fintype Ω] (p : Law Ω)

def prob (e : Ω → Prop) := ∑ x, if e x then p.mass x else 0

theorem positive (e : Ω → Prop) : 0 ≤ p.prob e :=
  Finset.sum_nonneg (fun x _ => by split <;> simp [p.nonneg])

theorem mono {e f : Ω → Prop} (h : ∀ x, e x → f x) : p.prob e ≤ p.prob f := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hh : e x
  · simp [hh,h x hh]
  · simp [hh]; split <;> simp [p.nonneg]

theorem certain {e : Ω → Prop} (h : ∀ x, e x) : p.prob e = 1 := by simp [prob,h,p.total]

theorem neg (e : Ω → Prop) : p.prob (fun x => ¬e x) = 1 - p.prob e := by
  rw [eq_sub_iff_add_eq,prob,prob,← Finset.sum_add_distrib,← p.total]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hh : e x <;> simp [hh]

theorem witness {e : Ω → Prop} (h : p.prob e < 1) : ∃ x, ¬e x := by
  by_contra! hn
  exact h.ne (p.certain hn)

theorem union [Fintype I] (e : I → Ω → Prop) :
    p.prob (fun x => ∃ i, e i x) ≤ ∑ i, p.prob (e i) := by
  unfold prob
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  have hn : ∀ i, 0 ≤ if e i x then p.mass x else 0 := fun i => by split <;> simp [p.nonneg]
  split
  · rename_i h
    obtain ⟨i,hi⟩ := h
    simpa [hi] using Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
  · exact Finset.sum_nonneg (fun j _ => hn j)

variable [Fintype I] [DecidableEq I] {X : I → Type} [∀ i, Fintype (X i)]

def product (ps : ∀ i, Law (X i)) : Law (∀ i, X i) where
  mass x := ∏ i, (ps i).mass (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (ps i).nonneg (x i))
  total := by rw [← Fintype.prod_sum]; simp [total]

theorem independent (ps : ∀ i, Law (X i)) (e : ∀ i, X i → Prop) :
    (product ps).prob (fun x => ∀ i, e i (x i)) = ∏ i, (ps i).prob (e i) := by
  unfold prob
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hh : ∀ i, e i (x i)
  · simp [hh,product]
  · obtain ⟨i,hi⟩ := not_forall.mp hh
    simp only [hh,↓reduceIte]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm

def copies (p : Law Ω) (n : ℕ) : Law (Fin n → Ω) := product (fun _ => p)

theorem miss (n : ℕ) (e : Ω → Prop) :
    (p.copies n).prob (fun x => ∀ i, ¬e (x i)) ≤ Real.exp (-(n : ℝ)*p.prob e) := by
  have he := independent (fun _ : Fin n => p) (fun _ x => ¬e x)
  change (p.copies n).prob _ = _ at he
  rw [he,Finset.prod_const,Finset.card_univ,Fintype.card_fin,neg_mul,← mul_neg,Real.exp_nat_mul]
  apply pow_le_pow_left₀ (p.positive _)
  rw [p.neg]
  linarith [Real.add_one_le_exp (-p.prob e)]

omit [DecidableEq I] in
theorem hitting (n : ℕ) (e : I → Ω → Prop) (bound : ℝ)
    (he : ∀ i, bound ≤ p.prob (e i))
    (hn : Fintype.card I * Real.exp (-(n : ℝ)*bound) < 1) :
    ∃ x : Fin n → Ω, ∀ i, ∃ j, e i (x j) := by
  let bad := fun i (x : Fin n → Ω) => ∀ j, ¬e i (x j)
  have hb : ∀ i, (p.copies n).prob (bad i) ≤ Real.exp (-(n : ℝ)*bound) := fun i =>
    (p.miss n (e i)).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (he i) (by simp)))
  have hh := ((p.copies n).union bad).trans (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  obtain ⟨x,hx⟩ := (p.copies n).witness (hh.trans_lt hn)
  exact ⟨x,fun i => by by_contra! h; exact hx ⟨i,h⟩⟩

end Law
end OAI.Geometry.Hirsch.Layer
