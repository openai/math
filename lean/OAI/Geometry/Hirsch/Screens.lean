import OAI.Geometry.Hirsch.Pins

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {Ω I : Type} [Fintype Ω]

theorem Law.either (p : Law Ω) (e f : Ω → Prop) :
    p.prob (fun x => e x ∨ f x) ≤ p.prob e + p.prob f := by
  unfold prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases he : e x <;> by_cases hf : f x <;> simp [he,hf,p.nonneg]

structure Thresholds (K : ℕ) where
  value : ℕ → ℝ
  positive : ∀ j, 0 < value j
  mono : Monotone value
  ratio : ∀ j < K, value j ≤ value (j+1)^2 * value K

namespace Pins

open Law

variable {p : Law Ω} (pins : Pins p I)

def cond (s : Finset I) : Law Ω where
  mass x := p.mass x * pins.density s x
  nonneg x := mul_nonneg (p.nonneg x) (mul_nonneg (inv_nonneg.mpr (pins.positive _).le) (ind_nonneg _))
  total := by
    change p.mean (pins.density s) = 1
    unfold density
    rw [mean_scale,mean_ind,pins.prob]
    exact inv_mul_cancel₀ (pins.positive s).ne'

@[simp] theorem cond_prob (e : Ω → Prop) (s : Finset I) : (pins.cond s).prob e = pins.given e s := by
  rw [← resolve,← mean_ind]
  unfold mean
  exact Finset.sum_congr rfl fun _ _ => by dsimp only [cond]; ring

variable {K : ℕ} (thr : Thresholds K) (e : Ω → Prop)

def Compatible (P : Finset I) : Prop :=
  ∀ S ⊆ P, S.card ≤ K → pins.given e S ≤ thr.value S.card

def Screen (x : Ω) : Prop := ¬e x ∧ pins.Compatible thr e (pins.success x)

theorem passes {x : Ω} (hs : pins.Screen thr e x) {P : Finset I} (hp : P ⊆ pins.success x) :
    pins.Compatible thr e P := fun _ hh => hs.2 _ (hh.trans hp)

theorem screen_cost {P : Finset I} (hk : P.card ≤ K) (hp : pins.Compatible thr e P) :
    pins.given (fun x => ¬pins.Screen thr e x) P ≤ (1 + (4 : ℝ)^K) * thr.value K := by
  let T := ↥P.powerset
  let bad := fun (S : T) (x : Ω) => S.val.card < K ∧ ∃ R : Finset I, Disjoint P R ∧ R.card ≤ K ∧
    R ⊆ pins.success x ∧ thr.value (S.val.card+1) ≤ pins.given e (S.val ∪ R)
  let q := pins.cond P
  have bound : ∀ S, q.prob (bad S) ≤ (2 : ℝ)^K * thr.value K := by
    intro S
    have hsub := Finset.mem_powerset.mp S.property
    by_cases hs : S.val.card < K
    swap
    · simp [bad,hs,Law.prob,(thr.positive K).le]
    let u := thr.value (S.val.card+1)
    have hu := thr.positive (S.val.card+1)
    apply le_of_mul_le_mul_left _ (sq_pos_of_pos hu)
    have hh := pins.conditional_tail hsub e K hu
    simp only [bad,hs,true_and,q,cond_prob]
    calc
      _ ≤ (2 : ℝ)^K * pins.given e S.val := hh
      _ ≤ (2 : ℝ)^K * (u^2 * thr.value K) := mul_le_mul_of_nonneg_left
        ((hp S.val hsub hs.le).trans (thr.ratio _ hs)) (by positivity)
      _ = _ := by unfold u; ring
  have cover : ∀ x, ¬pins.Screen thr e x → e x ∨ ∃ S, bad S x := by
    intro x hx
    by_cases he : e x
    · exact .inl he
    right
    have hn : ¬pins.Compatible thr e (pins.success x) := fun h => hx ⟨he,h⟩
    unfold Compatible at hn
    push Not at hn
    obtain ⟨J,hj,hk',hh⟩ := hn
    let S := J ∩ P
    have sub : S ⊆ P := Finset.inter_subset_right
    have proper : S ⊂ J := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.inter_subset_left,fun eq => hh.not_ge (hp J (eq ▸ sub) hk')⟩
    have hl := Finset.card_lt_card proper
    have join : S ∪ (J \ P) = J := by ext; simp [S]; tauto
    refine ⟨⟨S,Finset.mem_powerset.mpr sub⟩,hl.trans_le hk',J \ P,?_,
      (Finset.card_le_card Finset.sdiff_subset).trans hk',Finset.sdiff_subset.trans hj,?_⟩
    · exact Finset.disjoint_left.mpr fun _ h h' => (Finset.mem_sdiff.mp h').2 h
    · rw [join]
      exact (thr.mono hl).trans hh.le
  have hc : (Fintype.card T : ℝ) ≤ 2^K := by
    simp only [T,Fintype.card_coe,Finset.card_powerset,Nat.cast_pow,Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hk
  have cost : q.prob (fun x => ∃ S, bad S x) ≤ (4 : ℝ)^K * thr.value K := by
    calc
      _ ≤ ∑ S, q.prob (bad S) := q.union bad
      _ ≤ ∑ _ : T, (2 : ℝ)^K * thr.value K := Finset.sum_le_sum fun i _ => bound i
      _ ≤ 2^K * (2^K * thr.value K) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hc (mul_nonneg (by positivity) (thr.positive K).le)
      _ = _ := by rw [← mul_assoc,← mul_pow]; norm_num
  have low : q.prob e ≤ thr.value K := by
    rw [show q = pins.cond P from rfl,cond_prob]
    exact (hp _ Finset.Subset.rfl hk).trans (thr.mono hk)
  rw [← cond_prob]
  exact (q.mono cover).trans ((q.either _ _).trans (by linarith))

end Pins
end OAI.Geometry.Hirsch.Layer
