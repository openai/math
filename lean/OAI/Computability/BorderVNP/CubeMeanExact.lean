import OAI.Computability.BorderVNP.CubeMeanRows

/-! # Exact agreement of the sparse integer label scan with the conditional-mean chooser

A descriptor represents every one of its bits with the same endpoint labels. Each bin's integer
cache is its true conditional mean times the square of the number of labels. The omitted
nonincident part of the trial score is constant across candidate labels, so natural-number
comparisons preserve both the order and the public first-minimum tie rule.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.MeanChoice

open Balancing Finset
open scoped BigOperators

variable {C E A : Type*} [Fintype C] [DecidableEq C] [Fintype E] [Fintype A] {z : ℕ}

/-- Descriptor array consisting of all oriented cables and deliveries in their public order. -/
def trafficRows (src dst : E → C) (recv : A → C) (w : E → ℕ) (v : A → ℕ) : E ⊕ A → Traffic C :=
  Sum.elim (fun e => .cable (src e) (dst e) (w e)) (fun a => .delivery (recv a) (v a))

/-- Actual loads of all unit wires and data bits in the supplied descriptors. -/
abbrev bitLoads (src dst : E → C) (recv : A → C) (w : E → ℕ) (v : A → ℕ) :=
  loads (z := z) (fun b : Bits w => src b.1) (fun b : Bits w => dst b.1) (fun b : Bits v => recv b.1)

private theorem bits_mean {I : Type*} [Fintype I] (w : I → ℕ) (p : I → Pattern C (Fin (z+1)))
    (s : Finset C) (x : C → Fin (z+1)) :
    conditioned (load (fun b : Bits w => p b.1)) s x = ∑ i, (w i : ℝ)*pinnedChance (p i) s x := by
  unfold conditioned load
  rw [expect_sum_comm]
  simp_rw [expect_pinned_hit]
  exact sum_bits w (fun i => pinnedChance (p i) s x)

/-- The physical bin cache equals the conditioned mean of the expanded bits with common
denominator `(z+1)^2`, including bins whose two label symbols agree. -/
theorem cache_scaled (src dst : E → C) (recv : A → C) (w : E → ℕ) (v : A → ℕ) (hne : ∀ e, src e ≠ dst e)
    (s : Finset C) (x : C → Fin (z+1)) (j : Bins z) :
    (cache (trafficRows src dst recv w v) s x j : ℝ) =
      (z+1 : ℝ)^2 * mean (bitLoads src dst recv w v) s x j := by
  rcases j with ⟨u,t⟩|u
  · change _ = (z+1 : ℝ)^2 * conditioned (load (fun b : Bits w => cable src dst u t b.1)) s x
    rw [bits_mean, mul_sum]
    simp only [cache,Fintype.sum_sum_type,trafficRows,Sum.elim_inl,Sum.elim_inr,rowNat,
      Finset.sum_const_zero,add_zero,Nat.cast_sum]
    apply sum_congr rfl
    intro e _
    have scaled := factor_cable s x (src e) (dst e) u t (hne e)
    change (factor s x (src e) u * factor s x (dst e) t : ℕ) = (z+1 : ℝ)^2 * pinnedChance (cable src dst u t e) s x at scaled
    rw [Nat.mul_assoc,Nat.cast_mul,scaled]
    ring
  · change _ = (z+1 : ℝ)^2 * conditioned (load (fun b : Bits v => datum recv u b.1)) s x
    rw [bits_mean,mul_sum]
    simp only [cache,Fintype.sum_sum_type,trafficRows,Sum.elim_inl,Sum.elim_inr,rowNat,
      Finset.sum_const_zero,zero_add,Nat.cast_sum]
    apply sum_congr rfl
    intro a _
    have scaled := factor_datum s x (recv a) u
    change (factor s x (recv a) u : ℝ) = (z+1 : ℝ)*pinnedChance (datum recv u a) s x at scaled
    rw [Nat.cast_mul,Nat.cast_mul,scaled]
    push_cast
    ring

/-- Each row-score comparison is the corresponding comparison of the full real trial
scores; equality is therefore preserved too. -/
theorem scoreNat_le_iff (src dst : E → C) (recv : A → C) (w : E → ℕ) (v : A → ℕ) (hne : ∀ e, src e ≠ dst e)
    (s : Finset C) (x : C → Fin (z+1)) (c : C) (u t : Fin (z+1)) :
    scoreNat (trafficRows src dst recv w v) s x c u ≤ scoreNat (trafficRows src dst recv w v) s x c t ↔
      trial (bitLoads src dst recv w v) s x c u ≤ trial (bitLoads src dst recv w v) s x c t := by
  let rows := trafficRows src dst recv w v
  obtain ⟨off, hoff⟩ := exists_offset rows s x c
  have scaled (q : Fin (z+1)) : (scoreNat rows s x c q : ℝ)+off =
      (z+1 : ℝ)^4*trial (bitLoads src dst recv w v) s x c q := by
    calc (scoreNat rows s x c q : ℝ)+off =
           ∑ j, (cache rows s x j : ℝ)*(cache rows (insert c s) (Function.update x c q) j : ℝ) := by
             exact_mod_cast hoff q
         _ = _ := by
           dsimp only [rows,trial,dot]
           rw [mul_sum]
           apply sum_congr rfl
           intro j _
           rw [cache_scaled src dst recv w v hne,cache_scaled src dst recv w v hne]
           ring
  change scoreNat rows s x c u ≤ scoreNat rows s x c t ↔ _
  rw [← Nat.cast_le (α := ℝ), ← add_le_add_iff_right (off : ℝ), scaled u, scaled t]
  exact mul_le_mul_iff_right₀ (by positivity)

/-- A finite increasing-order scan preserves its exact first result whenever all score
comparisons agree, even in the presence of repeated minimal values. -/
theorem firstMinimum_of_compare {X Y : Type*} [LinearOrder X] [LinearOrder Y]
    (f : Fin (z+1) → X) (g : Fin (z+1) → Y) (h : ∀ a b, f a ≤ f b ↔ g a ≤ g b) :
    firstMinimum f = firstMinimum g := by
  have same (l : List (Fin (z+1))) : l.argmin f = l.argmin g := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.argmin_cons,List.argmin_cons,ih]
      cases l.argmin g with
      | none => rfl
      | some b =>
        have cmp : f b < f a ↔ g b < g a := lt_iff_not_ge.trans ((not_congr (h a b)).trans lt_iff_not_ge.symm)
        change (if f b < f a then some b else some a) = if g b < g a then some b else some a
        by_cases hlt : f b < f a
        · rw [ite_eq_left hlt,ite_eq_left (cmp.mp hlt)]
        · rw [ite_eq_right hlt,ite_eq_right (fun h => hlt (cmp.mpr h))]
  exact congrArg (fun m : Option (Fin (z+1)) => m.getD 0) (same _)

/-- An integer-only scan in public cell order, updating its existing cache after each pin. -/
def scanNat {I : Type*} [Fintype I] (rows : I → Traffic C) : List C → Finset C →
    (C → Fin (z+1)) → (Bins z → ℕ) → (C → Fin (z+1))
  | [], _, x, _ => x
  | c :: cs, s, x, old =>
    if c ∈ s then scanNat rows cs s x old else
      let u := firstMinimum (candidate rows s x c old)
      scanNat rows cs (insert c s) (Function.update x c u) (commit rows s x c u old)

/-- The returned labeling is exactly the one from the true conditioned-mean scan. -/
theorem scanNat_eq_follow (src dst : E → C) (recv : A → C) (w : E → ℕ) (v : A → ℕ) (hne : ∀ e, src e ≠ dst e)
    (cs : List C) (s : Finset C) (x : C → Fin (z+1)) :
    scanNat (trafficRows src dst recv w v) cs s x (cache (trafficRows src dst recv w v) s x) =
      follow (bitLoads src dst recv w v) cs s x := by
  induction cs generalizing s x with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c ∈ s
    · simpa only [scanNat,follow,ite_eq_left hc] using ih s x
    · have choose : firstMinimum (candidate (trafficRows src dst recv w v) s x c (cache (trafficRows src dst recv w v) s x)) =
          firstMinimum (trial (bitLoads src dst recv w v) s x c) :=
        firstMinimum_of_compare _ _ (scoreNat_le_iff src dst recv w v hne s x c)
      simp only [scanNat,follow,ite_eq_right hc,choose,commit_cache]
      exact ih _ _

end Cube.MeanChoice

end BorderVNP
end Computability
end OAI
