import OAI.Geometry.Hirsch.Fresh

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {I Bit : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I] {coin : Coins Bit}
  {n : ℕ} {w : Board I n} {tag : Stamp Bit I} {k width : ℕ} {L b : ℝ}

structure Foil (coin : Coins Bit) (tag : Stamp Bit I) (k : ℕ) (rate L b : ℝ) where
  index : Finset I → Bit
  age : ∀ s, tag.age (index s) = k
  keys : ∀ s, tag.keys (index s) = s
  barrier : ∀ s, ¬tag.pin (index s)
  bias : ∀ s, coin.bias (index s) = Real.exp ((-4*L/b)*rate^s.card)
  positive : 0 < b
  nonneg : 0 ≤ L

namespace Foil

variable {pins : Pins coin.law I} (f : Foil coin tag k pins.rate L b)
  (B : Finset (Finset I))

def bits := B.image f.index

omit [Fintype I] in
theorem weight : coin.weight (f.bits B) = Real.exp ((-4*L/b)*pins.mass B) := by
  unfold Coins.weight bits
  rw [Finset.prod_image (fun s _ t _ he => (f.keys s).symm.trans ((congrArg tag.keys he).trans (f.keys t)))]
  unfold Pins.mass Pins.weight
  rw [Finset.mul_sum,Real.exp_sum]
  exact Finset.prod_congr rfl fun s _ => f.bias s

omit [Fintype I] in
theorem low (h : pins.mass B ≤ 2*b) : Real.exp (-8*L) ≤ coin.weight (f.bits B) := by
  rw [f.weight,Real.exp_le_exp,div_mul_eq_mul_div,le_div_iff₀ f.positive]
  nlinarith only [mul_le_mul_of_nonneg_left h f.nonneg]

omit [Fintype I] in
theorem high (h : b/4 ≤ pins.mass B) : coin.law.prob (Coins.All (f.bits B)) ≤ Real.exp (-L) := by
  rw [coin.all_prob,f.weight,Real.exp_le_exp,div_mul_eq_mul_div,div_le_iff₀ f.positive]
  nlinarith only [mul_le_mul_of_nonneg_left h f.nonneg]

omit [Fintype I] in
theorem visible (i : I)
    (hh : ∀ s ∈ B, s.Nonempty ∧ ∀ j ∈ s, w.place j ∈ w.home width i ∧ w.rank j < w.rank i) :
    ∀ c ∈ f.bits B, ¬tag.pin c ∧ c ∈ tag.scope w k width i := by
  intro c hc
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hn,hh⟩ := hh s hs
  simp only [Stamp.scope,Board.zone,Set.mem_ofPred_eq,f.age,f.keys,le_refl,true_and]
  exact ⟨f.barrier _,⟨hn,fun j hj => (hh j hj).1⟩,fun j hj => (hh j hj).2.le⟩

theorem independent {raw : coin.Raw I} {rule : Coins.Rules raw} (hr : tag.Visible w rule k width)
    (hide s : Finset I) (q : w.Round) (area : Set ℕ) (d : Bool) (R : ℕ) (j : I)
    (hh : ∀ t ∈ B, t.Nonempty ∧ ∀ g ∈ t, w.rank j < w.rank g) :
    coin.law.Independent (Coins.All (f.bits B)) (q.Cover area d R (rule.watch hide s) j) := by
  apply coin.independent (s := (↑(f.bits B))ᶜ)
  · rw [compl_compl]; exact Coins.reads_all _
  apply Board.Round.reads_cover
  intro g _ hg
  apply (hr.watch hide s g).mono
  intro c hc hc'
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hc'
  obtain ⟨⟨u,hu⟩,hlt⟩ := hh t ht
  have := hc.2.2 u ((f.keys _).symm ▸ hu)
  exact (hlt _ hu).not_ge (this.trans hg.le)

end Foil

namespace Board.Ledger

variable {Ω : Type} [Fintype Ω] {p : Law Ω} {pins : Pins p I}
  {K : ℕ} {gamma alpha : ℝ} {gate : Trial.Gates pins w.place K gamma alpha}
  {old r : w.Round} {area : Set ℕ} {d : Bool} {D : Depths K} {M A : ℝ}
  (ledger : Ledger gate old area d D M A) {i : I}

theorem support (hi : w.place i ∈ area) {s : Finset I} (hs : s ∈ ledger.book r i (flat D.limit)) :
    s.Nonempty ∧ ∀ j ∈ s, w.place j ∈ area ∧ w.rank j < w.rank i := by
  let c := ledger.core r hi base
  have hc := ledger.cut hi base hs
  have h := c.refines _ hc.1
  exact ⟨h.nonempty c.inhabited,fun _ hj => ⟨Round.keys_inside h hc.2 hj,c.falls.older h hc.2 _ hj⟩⟩

end Board.Ledger

def price (t : ℝ) (j : ℕ) := t/4 * 2^j

theorem price_low {t : ℝ} (ht : 0 < t) (j : ℕ) : t/4 ≤ price t j :=
  le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))

theorem buckets {t m : ℝ} {J : ℕ} (hl : t/4 ≤ m) (hh : m < price t J) :
    ∃ j : Fin J, price t j ≤ m ∧ m < 2*price t j := by
  induction J with
  | zero => simp [price] at hh; linarith
  | succ J ih =>
    by_cases he : m < price t J
    · obtain ⟨j,hj⟩ := ih he
      exact ⟨j.castSucc,hj⟩
    · refine ⟨Fin.last J,le_of_not_gt he,?_⟩
      simpa [price,pow_succ',mul_left_comm] using hh

def bucket (t : ℝ) (J : ℕ) (m : ℝ) : Option (Fin J) :=
  if h : ∃ j : Fin J, price t j ≤ m ∧ m < 2*price t j then some h.choose else none

theorem bucket_high {t m : ℝ} {J : ℕ} {j : Fin J} (h : bucket t J m = some j) :
    price t j ≤ m ∧ m < 2*price t j := by
  unfold bucket at h
  split at h
  · rename_i hh; exact Option.some.inj h ▸ hh.choose_spec
  · contradiction

theorem bucket_low {t m : ℝ} {J : ℕ} (hh : m < price t J) (h : bucket t J m = none) : m < t/4 := by
  by_contra! he
  simp [bucket,buckets he hh] at h

end OAI.Geometry.Hirsch.Layer
