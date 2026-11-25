import OAI.Geometry.Hirsch.StateCuts

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

variable {L V K k : ℕ} {code : Bundles L V}

def micro (s : Fin L) (j : Fin k) := s.val*(k+2)+1+j.val

theorem micro_bound (s : Fin L) (j : Fin k) : micro s j < L*(k+2) := by
  have hh := Nat.mul_le_mul_right (k+2) s.isLt
  unfold micro
  nlinarith [j.isLt]

theorem micro_lt {s t : Fin L} (hs : s < t) (i j : Fin k) : micro s i < micro t j := by
  have hh := Nat.mul_le_mul_right (k+2) hs
  unfold micro
  nlinarith [i.isLt]

structure StateSequence (code : Bundles L V) (K k : ℕ) (q : ℝ) where
  states : ℕ → Finset (Values V)
  count : ∀ j, (states j).card ≤ K
  inhabited : ∀ j, (states j).Nonempty
  nonneg : ∀ j x, x ∈ states j → 0 ≤ x
  identifies : ∀ (s : Fin L) (i : Fin k) x, x ∈ states (micro s i) → code.Identifies s x
  merge : ∀ j, j+2 < L*(k+2) → ∀ x ∈ states j, ∀ y ∈ states (j+2),
    ∃ z ∈ states (j+1), ∀ l, z l ≤ q * max (x l) (y l)

def NumericalLayers : Prop :=
  ∀ rate : ℕ, ∃ L V K : ℕ, 2 ≤ L ∧ 0 < V ∧ (2*V)^rate ≤ L ∧
    ∃ code : Bundles L V, ∀ k, 0 < k → Nonempty (StateSequence code K k (1/4))

namespace StateSequence

variable {q : ℝ} (seq : StateSequence code K k q)

include seq in
theorem power (n : ℕ) (hn : n ≠ 0) : Nonempty (StateSequence code K k (q^n)) := by
  classical
  let f := fun x : Values V => fun l => (x l)^n
  refine ⟨{
    states := fun j => (seq.states j).image f,
    count := fun j => Finset.card_image_le.trans (seq.count j),
    inhabited := fun j => (seq.inhabited j).image _,
    nonneg := ?_, identifies := ?_, merge := ?_ }⟩
  · intro j _ hx'
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hx'
    exact fun l => pow_nonneg (seq.nonneg _ _ hx l) _
  · intro s i _ hx'
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hx'
    simpa [Bundles.Identifies,f,hn] using seq.identifies s i x hx
  · intro j hj _ hx' _ hy'
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hx'
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hy'
    obtain ⟨z,hz,hh⟩ := seq.merge j hj x hx y hy
    refine ⟨f z,Finset.mem_image_of_mem _ hz,fun l => ?_⟩
    have hb := pow_le_pow_left₀ (seq.nonneg _ _ hz l) (hh l) n
    rw [mul_pow] at hb
    unfold f
    rcases le_total (x l) (y l) with hl | hl
    · simpa [max_eq_right hl,max_eq_right (pow_le_pow_left₀ (seq.nonneg _ _ hx l) hl n)] using hb
    · simpa [max_eq_left hl,max_eq_left (pow_le_pow_left₀ (seq.nonneg _ _ hy l) hl n)] using hb

def minVal (c : Values V) (j : ℕ) := (seq.states j).inf' (seq.inhabited j) (dot c)

theorem min_le (c : Values V) {j x} (hx : x ∈ seq.states j) : seq.minVal c j ≤ dot c x :=
  Finset.inf'_le _ hx

theorem min_attained (c : Values V) (j : ℕ) : ∃ x ∈ seq.states j, seq.minVal c j = dot c x :=
  Finset.exists_mem_eq_inf' _ _

theorem min_nonneg {c : Values V} (hc : 0 ≤ c) (j : ℕ) : 0 ≤ seq.minVal c j := by
  obtain ⟨x,hx,he⟩ := seq.min_attained c j
  rw [he,← map_zero (dot c)]
  exact dot_mono hc (seq.nonneg _ _ hx)

theorem min_merge {c : Values V} (hc : 0 ≤ c) (hq : 0 ≤ q) {j : ℕ} (hj : j+2 < L*(k+2)) :
    seq.minVal c (j+1) ≤ q * (seq.minVal c j + seq.minVal c (j+2)) := by
  obtain ⟨x,hx,he⟩ := seq.min_attained c j
  obtain ⟨y,hy,hf⟩ := seq.min_attained c (j+2)
  obtain ⟨z,hz,hh⟩ := seq.merge j hj x hx y hy
  have hb : z ≤ q • (x+y) := fun l => (hh l).trans (mul_le_mul_of_nonneg_left
    (max_le (le_add_of_nonneg_right (seq.nonneg _ _ hy l)) (le_add_of_nonneg_left (seq.nonneg _ _ hx l))) hq)
  simpa [he,hf,mul_add] using (seq.min_le c hz).trans (dot_mono hc hb)

theorem min_middle {c : Values V} (hc : 0 ≤ c) (hq : 0 ≤ q) (hhalf : q < 1/2)
    {i j m : ℕ} (h₁ : i < j) (h₂ : j < m) (hm : m < L*(k+2)) :
    seq.minVal c j ≤ 2*q*max (seq.minVal c i) (seq.minVal c m) := by
  let f := seq.minVal c
  obtain ⟨p,hp,ht⟩ := (Finset.Icc i m).exists_max_image f (by simp; omega)
  have bound : ∀ a, i ≤ a → a ≤ m → f a ≤ f p := fun a ha hb => ht a (Finset.mem_Icc.mpr ⟨ha,hb⟩)
  have interior : ∀ a, i < a → a < m → f a ≤ 2*q*f p := by
    intro a ha hb
    have hh := seq.min_merge hc hq (j := a-1) (by omega)
    rw [show a-1+1 = a by omega,show a-1+2 = a+1 by omega] at hh
    exact hh.trans (by
      change q*(f (a-1)+f (a+1)) ≤ _
      linarith [mul_le_mul_of_nonneg_left (bound (a-1) (by omega) (by omega)) hq,
        mul_le_mul_of_nonneg_left (bound (a+1) (by omega) (by omega)) hq])
  apply (interior j h₁ h₂).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  by_cases he : p = i
  · subst p; exact le_max_left ..
  by_cases he' : p = m
  · subst p; exact le_max_right ..
  have hp' := Finset.mem_Icc.mp hp
  have hh := interior p (by omega) (by omega)
  have hn : f p ≤ 0 := by nlinarith
  exact hn.trans ((seq.min_nonneg hc i).trans (le_max_left ..))

end StateSequence
end OAI.Geometry.Hirsch.Layer
