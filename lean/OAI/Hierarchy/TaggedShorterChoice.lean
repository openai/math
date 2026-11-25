import OAI.Hierarchy.TaggedShorterBudget
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace OAI
/-! # Uniform choice of the shorter-call menu and its physical slots -/

namespace Hierarchy.TaggedShorterBudget

noncomputable section

open Real Finset Set

/-- Simultaneous approximation of the protocol parameters, at an already fixed
upper width exponent. The predicate can carry the protocol existence theorem. -/
def Cofinal (P : ℝ → ℝ → ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ η L₀ : ℝ, 0<η → 0<L₀ → ∃ p q Q σ L : ℝ,
    P p q Q σ L ∧ p≤1+η ∧ q≤η ∧ 1/η≤Q ∧ σ≤η ∧ L₀≤L

/-- The protocol theorem for every admissible real parameter tuple implies
the simultaneous cofinal form used below. -/
theorem Cofinal.of_all {P : ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (all : ∀ p q Q σ L, 1<p → 0<q → q<Q → 0<σ → 0<L → P p q Q σ L) : Cofinal P := by
  intro η L₀ hη hL
  let Q := max (1/η) (η/2+1)
  have hQ : η/2<Q := (show η/2<η/2+1 by linarith).trans_le (le_max_right _ _)
  exact ⟨1+η/2,η/2,Q,η/2,L₀,all _ _ _ _ _ (by linarith) (by positivity) hQ (by positivity) hL,
    by linarith,by linarith,le_max_left _ _,by linarith,le_rfl⟩

/-- All constants except the dyadic width floor are chosen before the
protocol's linear bound on the number of available transport positions. -/
structure Choice (u : ℝ→ℝ) (A ε p q Q σ L δ η ξ : ℝ) : Prop where
  delta_pos : 0<δ
  eta_pos : 0<η
  xi_pos : 0<ξ
  one_le_price : 1≤L
  costly : 11≤ξ*L^δ
  sum_price : 21*ξ*(1/(1-(1/2:ℝ)^δ))^2≤ε
  exponents : ∀ a∈Icc 1 A,
    let b := -deriv u a
    let v := u a+a*b
    let θ := b+δ
    0<θ ∧ δ≤θ ∧ θ<1 ∧ p*θ≤v-δ ∧ 0≤v-δ ∧ σ≤v-δ ∧
      q≤1/θ-1 ∧ 1/θ-1≤Q ∧ η≤1-θ

/-- Choose one protocol after fixing uniform interpolation margins. The smooth
profile lemma supplies precisely these margins on each compact width range. -/
theorem choose_of_prices {u : ℝ→ℝ} {A ε : ℝ}
    (margins : ∃ δ η : ℝ, 0<δ ∧ 0<η ∧ ∀ a∈Icc 1 A,
      let b := -deriv u a
      let v := u a+a*b
      let θ := b+δ
      0<θ ∧ δ≤θ ∧ θ<1 ∧ (1+η)*θ≤v-δ ∧ η≤v-δ ∧
        η≤1/θ-1 ∧ 1/θ-1≤1/η ∧ η≤1-θ)
    (hε : 0<ε) {P : ℝ → ℝ → ℝ → ℝ → ℝ → Prop} (protocols : Cofinal P) :
    ∃ δ η ξ p q Q σ L : ℝ, P p q Q σ L ∧ Choice u A ε p q Q σ L δ η ξ := by
  obtain ⟨δ,η,hδ,hη,prices⟩ := margins
  let g := 1/(1-(1/2:ℝ)^δ)
  have hg : 0<g := one_div_pos.mpr (sub_pos.mpr (rpow_lt_one (by norm_num) (by norm_num) hδ))
  let ξ := ε/(21*g^2)
  have hξ : 0<ξ := div_pos hε (by positivity)
  let L₀ := max 1 ((11/ξ)^(1/δ))
  have hL₀ : (0:ℝ)<L₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨p,q,Q,σ,L,hP,hp,hq,hQ,hσ,hL⟩ := protocols η L₀ hη hL₀
  refine ⟨δ,η,ξ,p,q,Q,σ,L,hP,hδ,hη,hξ,(le_max_left _ _).trans hL,?_,?_,?_⟩
  · have high : (11/ξ)^(1/δ) ≤ L := (le_max_right _ _).trans hL
    have power := rpow_le_rpow (rpow_nonneg (show 0≤11/ξ by positivity) _) high hδ.le
    rw [←rpow_mul (show 0≤11/ξ by positivity),one_div_mul_cancel hδ.ne',rpow_one] at power
    simpa only [mul_comm] using (div_le_iff₀ hξ).mp power
  · change 21*ξ*g^2≤ε
    dsimp only [ξ]
    apply le_of_eq
    field_simp [hg.ne']
  · intro a ha
    obtain ⟨t,d,upper,win,e,lo,hi,j⟩ := prices a ha
    exact ⟨t,d,upper,(mul_le_mul_of_nonneg_right hp t.le).trans win,hη.le.trans e,
      hσ.trans e,hq.trans lo,hi.trans hQ,j⟩

variable {u : ℝ→ℝ} {A ε p q Q σ L δ η ξ : ℝ}

/-- A common menu and type fraction for every admissible width and summand of
this protocol. Width floor depth m is independent of the summand and n. -/
theorem Choice.active_types (h : Choice u A ε p q Q σ L δ η ξ) {C : ℝ} (hC : 0≤C) :
    ∃ m : ℕ, ∀ a∈Icc 1 A, ∀ (ι : Type*) (links : Finset ι) (scale : ι→ℕ)
      (l y : ι→ℝ) (n : ℝ), 0≤n → (links.card:ℝ)≤C*n →
      (∀ i∈links,0<l i ∧ 0≤y i ∧ L*dyadic (scale i)^σ≤l i) →
      (∑ i∈links,(l i*y i+L*capacity p q Q (dyadic (scale i)) (l i))≤11*n) →
      ∀ j k, (active links scale y m j k : ℝ) ≤
        fraction ξ (u a+a*(-deriv u a)-δ) (1-(-deriv u a)-δ) j k*n := by
  obtain ⟨m,hfloor⟩ := exists_floor h.eta_pos h.xi_pos hC
  refine ⟨m,?_⟩
  intro a ha ι links scale l y n hn number length budget j k
  obtain ⟨t,d,upper,win,e,s,lo,hi,z⟩ := h.exponents a ha
  rw [show 1-(-deriv u a)-δ = 1-(-deriv u a+δ) by ring]
  apply active_le
  exact rounded_total links scale y l h.one_le_price t upper.le d z win lo hi s e
    h.xi_pos.le hn hC h.costly hfloor number length budget

/-- The same allocation works on an arbitrary protocol menu of positive scale
indices. Only types that occur in the menu contribute installed slots. -/
theorem Choice.physical_menu (h : Choice u A ε p q Q σ L δ η ξ) {a n : ℝ}
    (ha : a∈Icc 1 A) (hn : 0≤n) (menu : Finset (ℕ×ℕ)) (K : ℕ×ℕ→ℕ)
    (batch : ∀ i∈menu,0<K i ∧ (K i:ℝ)≤3*ξ*n) :
    let b := -deriv u a
    let v := u a+a*b
    let S := fun i : ℕ×ℕ => installed (fraction ξ (v-δ) (1-b-δ) i.1 i.2) n (K i)
    (∀ i∈menu,18*ξ*n ≤ (S i:ℝ)) ∧
      ∑ i∈menu,(S i:ℝ)*(dyadic i.1^v*dyadic i.2^(1-b)) ≤ ε*n := by
  intro b v S
  obtain ⟨_,_,upper,_,e,_,_,_,_⟩ := h.exponents a ha
  have f : 0≤1-b-δ := by dsimp [b]; linarith
  have low (i : ℕ×ℕ) : 3*ξ*n≤fraction ξ (v-δ) (1-b-δ) i.1 i.2*n :=
    mul_le_mul_of_nonneg_right (fraction_lower h.xi_pos.le e f i.1 i.2) hn
  have slots (i : ℕ×ℕ) (hi : i∈menu) :=
    installed_bounds (fraction_pos h.xi_pos (v-δ) (1-b-δ) i.1 i.2).le hn
      (batch i hi).1 ((batch i hi).2.trans (low i))
  constructor
  · intro i hi
    change _ ≤ (installed (fraction ξ (v-δ) (1-b-δ) i.1 i.2) n (K i):ℝ)
    nlinarith [(slots i hi).1,low i]
  · let J := menu.sup Prod.fst + 1
    let W := menu.sup Prod.snd + 1
    have inside : menu ⊆ range J ×ˢ range W := by
      intro i hi
      exact Finset.mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hi)),
        mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hi))⟩
    let count := fun j k : ℕ => if (j,k)∈menu then S (j,k) else 0
    let price := fun i : ℕ×ℕ => (count i.1 i.2:ℝ)*(dyadic i.1^v*dyadic i.2^(1-b))
    have cap (j k : ℕ) : (count j k:ℝ)≤7*fraction ξ (v-δ) (1-b-δ) j k*n := by
      by_cases i : (j,k)∈menu
      · simpa only [count,ite_eq_left i,S] using (slots (j,k) i).2
      · simp only [count,ite_eq_right i,Nat.cast_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) (fraction_pos h.xi_pos _ _ _ _).le) hn
    calc
      _ = ∑ i∈menu,price i := by
        apply sum_congr rfl
        intro i hi
        simp [price,count,hi]
      _ ≤ ∑ i∈range J ×ˢ range W,price i :=
        sum_le_sum_of_subset_of_nonneg inside fun i _ _ => mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (rpow_nonneg (dyadic_pos _).le _) (rpow_nonneg (dyadic_pos _).le _))
      _ ≤ 21*ξ*n*(1/(1-(1/2:ℝ)^δ))^2 := by
        rw [sum_product]
        exact installed_total h.xi_pos.le hn h.delta_pos J W count (fun j _ k _ => cap j k)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right h.sum_price hn]

/-- At every installed width, the field can hold a complete linear-size
metadata word for all sufficiently large h whenever w grows as h^(1+κ). -/
theorem metadata_fits (m : ℕ) {κ C : ℝ} (hκ : 0<κ) (hC : 0≤C) :
    ∃ H₀ : ℝ, ∀ (h w D k : ℕ), H₀≤h → (h:ℝ)^(1+κ)≤w → (D:ℝ)≤C*h →
      k≤m → D≤⌈dyadic k*w⌉₊ := by
  let H₀ := max 1 ((C/dyadic m)^(1/κ))
  refine ⟨H₀,?_⟩
  intro h w D k high wide word hk
  have hp : 0<(h:ℝ) := zero_lt_one.trans_le ((le_max_left _ _).trans high)
  have c0 := div_nonneg hC (dyadic_pos m).le
  have cutoff : (C/dyadic m)^(1/κ) ≤ h := (le_max_right _ _).trans high
  have pwr := rpow_le_rpow (rpow_nonneg c0 _) cutoff hκ.le
  rw [←rpow_mul c0,one_div_mul_cancel hκ.ne',rpow_one] at pwr
  have width := (div_le_iff₀ (dyadic_pos m)).mp pwr
  have yd : dyadic m≤dyadic k := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  rw [rpow_add hp,rpow_one] at wide
  have enough : (D:ℝ)≤dyadic k*w := calc
    _ ≤ C*h := word
    _ ≤ dyadic m*((h:ℝ)*(h:ℝ)^κ) := by nlinarith [mul_le_mul_of_nonneg_right width hp.le]
    _ ≤ _ := mul_le_mul yd wide (mul_nonneg hp.le (rpow_nonneg hp.le _)) (dyadic_pos k).le
  exact_mod_cast enough.trans (Nat.le_ceil _)

/-- The metadata and payload calls may use distinct physical banks with shared
tags. Choosing the numerical protocol at ε/2 pays for both banks in full. -/
theorem Choice.paired_menu (h : Choice u A (ε/2) p q Q σ L δ η ξ) {a n : ℝ}
    (ha : a∈Icc 1 A) (hn : 0≤n) (menu : Finset (ℕ×ℕ)) (K : ℕ×ℕ→ℕ)
    (batch : ∀ i∈menu,0<K i ∧ (K i:ℝ)≤3*ξ*n) :
    let b := -deriv u a
    let v := u a+a*b
    let S := fun i : ℕ×ℕ => 2*installed (fraction ξ (v-δ) (1-b-δ) i.1 i.2) n (K i)
    (∀ i∈menu,36*ξ*n ≤ (S i:ℝ)) ∧
      ∑ i∈menu,(S i:ℝ)*(dyadic i.1^v*dyadic i.2^(1-b)) ≤ ε*n := by
  intro b v S
  let base := fun i : ℕ×ℕ => installed (fraction ξ (v-δ) (1-b-δ) i.1 i.2) n (K i)
  obtain ⟨lower,bound⟩ := h.physical_menu ha hn menu K batch
  constructor
  · intro i hi
    have each : 18*ξ*n ≤ (base i:ℝ) := lower i hi
    change 36*ξ*n ≤ ((2*base i:ℕ):ℝ)
    push_cast
    linarith
  · have total : ∑ i∈menu,(base i:ℝ)*(dyadic i.1^v*dyadic i.2^(1-b)) ≤ ε/2*n := bound
    calc
      _ = 2*(∑ i∈menu,(base i:ℝ)*(dyadic i.1^v*dyadic i.2^(1-b))) := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro i _
        change ((2*base i:ℕ):ℝ)*_ = _
        push_cast
        ring
      _ ≤ _ := by linarith

/-- Buying whole modules gives a uniform linear lower bound per type as well
as the requested εn weighted upper bound for the complete rectangle. -/
theorem Choice.physical_slots (h : Choice u A ε p q Q σ L δ η ξ) {a n : ℝ}
    (ha : a∈Icc 1 A) (hn : 0≤n) (J W : ℕ) (K : ℕ→ℕ→ℕ)
    (batch : ∀ j∈range J,∀ k∈range W,0<K j k ∧ (K j k:ℝ)≤3*ξ*n) :
    let b := -deriv u a
    let v := u a+a*b
    let S := fun j k => installed (fraction ξ (v-δ) (1-b-δ) j k) n (K j k)
    (∀ j∈range J,∀ k∈range W,18*ξ*n ≤ (S j k:ℝ)) ∧
      ∑ j∈range J,∑ k∈range W,(S j k:ℝ)*(dyadic j^v*dyadic k^(1-b)) ≤ ε*n := by
  intro b v S
  obtain ⟨lower,upper⟩ := h.physical_menu ha hn (range J ×ˢ range W) (fun i=>K i.1 i.2)
    (fun i hi=>batch i.1 (Finset.mem_product.mp hi).1 i.2 (Finset.mem_product.mp hi).2)
  refine ⟨fun j hj k hk=>lower (j,k) (Finset.mk_mem_product hj hk),?_⟩
  rw [sum_product] at upper
  exact upper

end
end Hierarchy.TaggedShorterBudget

end OAI
