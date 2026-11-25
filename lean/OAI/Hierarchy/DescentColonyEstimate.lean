import OAI.Hierarchy.DescentColonyLeaves
import OAI.Hierarchy.DescentColonyLoads
import OAI.Hierarchy.DescentColonyMarks
import OAI.Hierarchy.DescentColonySeries
import OAI.Hierarchy.DescentColonyGrowth

namespace OAI
/-! # Expected number of actual propagated leaves under one shared binary layout -/

namespace Hierarchy.DescentColonies

open DescentGL DescentBaseVariance
open scoped BigOperators Classical
noncomputable section

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

private theorem shift_sum (f : ℕ → ℕ) (d n : ℕ) (early : ∀ j<d,f j=0) :
    (∑ j∈Finset.range n,f j) ≤ ∑ s∈Finset.range n,f (d+s) := by
  have extend := Finset.sum_le_sum_of_subset_of_nonneg (f:=f)
    (Finset.range_mono (show n≤d+n by omega)) (fun _ _ _ => Nat.zero_le _)
  have first : (∑ j∈Finset.range d,f j)=0 := Finset.sum_eq_zero fun j hj=>early j (Finset.mem_range.mp hj)
  rwa [Finset.sum_range_add,first,zero_add] at extend

private def gapCount (weight : V → Block k → ℕ) (adj : V → V → Prop) (D a B : ℕ)
    (w : V) (d s : ℕ) :=
  if d+s≤k then (coverAt weight adj D a B w d (d+s)).card else 0

private theorem leaves_le_gaps (weight : V → Block k → ℕ) (adj : V → V → Prop) (D a B : ℕ)
    (limit : ∀v i,weight v i≤B) (positive : 0<D) :
    (leaves weight adj D a B limit).card ≤ Fintype.card V+
      2*∑ d∈Finset.range k,∑ w,∑ s∈Finset.range (k+1),gapCount weight adj D a B w d s := by
  apply (leaf_count weight adj D a B limit).trans
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  apply Finset.sum_le_sum
  intro d _
  apply (Finset.card_le_card (split_covered weight adj D a B limit positive d)).trans
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro w _
  apply Finset.card_biUnion_le.trans
  let f (j : ℕ) := if j≤k then (coverAt weight adj D a B w d j).card else 0
  have earlier (j : ℕ) (hj : j<d) : f j=0 := by simp [f,coverAt,Nat.not_le_of_gt hj]
  calc
    _ = ∑ j∈Finset.range (k+1),f j := Finset.sum_congr rfl fun j hj =>
      (ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).symm
    _ ≤ _ := shift_sum f d (k+1) earlier

private theorem avg_le {P : Type*} [Fintype P] (f g : P → ℝ) (le : ∀I,f I≤g I) :
    average f≤average g := div_le_div_of_nonneg_right (Finset.sum_le_sum fun p _=>le p) (by positivity)

private theorem avg_range {P : Type*} [Fintype P] (n : ℕ) (f : P → ℕ → ℝ) :
    average (fun L => ∑ i∈Finset.range n,f L i)=∑ i∈Finset.range n,average (fun L=>f L i) := by
  unfold average
  rw [Finset.sum_comm,Finset.sum_div]

private theorem expected_gap {P : Type*} [Fintype P] [Nonempty P] (family : P → Layout k)
    (pairs : ∀ {j : ℕ} (hj : j≤k), PairBound (fun p => dyadicLayout hj (family p)))
    (weight : V → Block k → ℕ) (adj : V → V → Prop) (D a B Δ : ℕ)
    (limit : ∀v i,weight v i≤B) (degree : ∀v,(next adj v).card≤Δ) (branch : 2≤Δ)
    (scale_pos : 0<2^a*B) (two : 2≤2^a) (w : V) (d s : ℕ) :
    average (fun p : P => (gapCount (rearrangedLoad weight (family p)) adj D a B w d s:ℝ)) ≤
      (2*(Δ:ℝ)^(s/D))*min ((2:ℝ)^d)
        (2*(∑ i,normalized weight (2^a*B:ℕ) w i)^2/2^(s+d)) := by
  let x := normalized weight (2^a*B:ℕ) w
  by_cases valid : d+s≤k
  · let bins := fun p : P => markedBins (dyadicLayout valid (family p)) x
    have bound (p : P) : gapCount (rearrangedLoad weight (family p)) adj D a B w d s ≤
        (2*Δ^(s/D))*min (2^d) (bins p).card := by
      have marks : (initialIds (rearrangedLoad weight (family p)) (2^a*B) w (d+s)).card≤(bins p).card := by
        simpa only [one_mul,Nat.cast_one,bins,markedBins,x] using
          initialIds_le_normalized weight (2^a*B) 1 scale_pos w valid (family p)
      have cap := cover_card (rearrangedLoad weight (family p)) adj D a B degree branch w (Nat.le_add_right d s) valid
      rw [min_comm] at cap
      simpa only [gapCount,ite_eq_left valid,Nat.add_sub_cancel_left] using
        cap.trans (Nat.mul_le_mul_left _ (min_le_min_left (2^d) marks))
    have nonnegative (i) : 0≤x i := by dsimp [x,normalized]; positivity
    have half (i) : x i ≤ 1/2 := by
      have h : 2*weight w i ≤ 2^a*B := Nat.mul_le_mul two (limit w i)
      have hh : (2:ℝ)*(weight w i:ℝ) ≤ (2^a*B:ℕ) := by exact_mod_cast h
      apply (div_le_iff₀ (by exact_mod_cast scale_pos : (0:ℝ)<(2^a*B:ℕ))).mpr
      linarith
    have expected := ancestor_expectation ((2:ℝ)^d) (fun p => dyadicLayout valid (family p)) (pairs valid) x nonnegative half
    calc
      _ ≤ average (fun p : P => (2*(Δ:ℝ)^(s/D))*min ((2:ℝ)^d) ((bins p).card:ℝ)) :=
        avg_le _ _ fun p => by exact_mod_cast bound p
      _ = (2*(Δ:ℝ)^(s/D))*average (fun p : P => min ((2:ℝ)^d) ((bins p).card:ℝ)) := average_mul _ _
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa [bins,x,Block,add_comm d s] using expected
  · simp only [gapCount,ite_eq_right valid,Nat.cast_zero,average_const]
    positivity

private theorem avg_const_add {P : Type*} [Fintype P] [Nonempty P] (c : ℝ) (f : P → ℝ) :
    average (fun p=>c+f p)=c+average f := by
  calc
    _ = average (fun _ : P => c)+average f := by
      simp only [average,Finset.sum_add_distrib,add_div]
    _ = _ := by rw [average_const]

private theorem all_gaps (x : ℝ) (hx : 0≤x) (k D Δ : ℕ)
    (growth : (∑s∈Finset.range (k+1),(Δ:ℝ)^(s/D)/(Real.sqrt 2)^s)≤10) :
    (∑s∈Finset.range (k+1), ∑d∈Finset.range k, (2*(Δ:ℝ)^(s/D))*
      min ((2:ℝ)^d) (2*x^2/2^(s+d))) ≤ 120*x := by
  calc
    _ ≤ ∑s∈Finset.range (k+1),(2*(Δ:ℝ)^(s/D))*(4*Real.sqrt 2*x/(Real.sqrt 2)^s) := by
      apply Finset.sum_le_sum
      intro s _
      rw [←Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (depth_gap_sum x hx s k) (by positivity)
    _ = (8*Real.sqrt 2*x)*(∑s∈Finset.range (k+1),(Δ:ℝ)^(s/D)/(Real.sqrt 2)^s) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    _ ≤ (8*Real.sqrt 2*x)*10 := mul_le_mul_of_nonneg_left growth (by positivity)
    _ ≤ _ := by
      have root : Real.sqrt 2≤3/2 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
      nlinarith [mul_nonneg (sub_nonneg.mpr root) hx]

/-- Expected count of the actual native colony leaves at all positions in one
group. The coefficient is independent of the degree and the number of blocks. -/
theorem expected_colonies_family {P : Type*} [Fintype P] [Nonempty P] (family : P → Layout k)
    (pairs : ∀ {j : ℕ} (hj : j≤k), PairBound (fun p => dyadicLayout hj (family p)))
    (weight : V → Block k → ℕ) (adj : V → V → Prop) (a B Δ : ℕ)
    (limit : ∀v i,weight v i≤B) (degree : ∀v,(next adj v).card≤Δ) (branch : 2≤Δ)
    (scale_pos : 0<2^a*B) (two : 2≤2^a) :
    let D := 32*Nat.clog 2 (2*Δ)
    average (fun p : P => ((leaves (rearrangedLoad weight (family p)) adj D a B
        (fun v i=>limit v ((rearrange (family p)).symm i))).card : ℝ)) ≤
      Fintype.card V + 240*(∑ w,∑i,normalized weight (2^a*B:ℕ) w i) := by
  let D := 32*Nat.clog 2 (2*Δ)
  let count (p : P) (w : V) (d s : ℕ) : ℝ := gapCount (rearrangedLoad weight (family p)) adj D a B w d s
  let total (w : V) := ∑ i,normalized weight (2^a*B:ℕ) w i
  let term (w : V) (s d : ℕ) := (2*(Δ:ℝ)^(s/D))*min ((2:ℝ)^d) (2*(total w)^2/2^(s+d))
  have sh (p : P) := leaves_le_gaps (rearrangedLoad weight (family p)) adj D a B
    (fun v i=>limit v ((rearrange (family p)).symm i)) (DescentColonyGrowth.positive_gap Δ branch)
  calc
    _ ≤ average (fun L : P => (Fintype.card V:ℝ)+2*
          ∑d∈Finset.range k,∑w,∑s∈Finset.range (k+1),count L w d s) :=
      avg_le _ _ fun L=>by dsimp only [count]; exact_mod_cast sh L
    _ = Fintype.card V + 2*(∑d∈Finset.range k,∑w,∑s∈Finset.range (k+1),average (fun L=>count L w d s)) := by
      rw [avg_const_add,average_mul,avg_range]
      simp_rw [average_sum,avg_range]
    _ ≤ Fintype.card V+2*(∑d∈Finset.range k,∑w,∑s∈Finset.range (k+1),term w s d) := by
      gcongr with d _ w _ s _
      exact expected_gap family pairs weight adj D a B Δ limit degree branch scale_pos two w d s
    _ = Fintype.card V+2*(∑w,∑s∈Finset.range (k+1),∑d∈Finset.range k,term w s d) := by
      congr 2
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun w _ => Finset.sum_comm
    _ ≤ Fintype.card V+2*(∑ w,120*total w) := by
      gcongr with w _
      have hx : 0≤total w := Finset.sum_nonneg fun i _ => by dsimp [normalized]; positivity
      exact all_gaps (total w) hx k D Δ (DescentColonyGrowth.sum_gap_growth Δ (k+1) branch)
    _ = _ := by rw [←Finset.mul_sum]; dsimp only [total]; ring

/-- A single permutation of the block IDs, shared across all groups and
positions, attains the bound for the sum of the actual leaf counts. -/
theorem exists_shared_colonies_family {P : Type*} [Fintype P] [Nonempty P] (family : P → Layout k)
    (pairs : ∀ {j : ℕ} (hj : j≤k), PairBound (fun p => dyadicLayout hj (family p)))
    {G : Type*} [Fintype G] (weight : G → V → Block k → ℕ)
    (adj : V → V → Prop) (a B Δ : ℕ) (limit : ∀ g v i,weight g v i≤B)
    (degree : ∀v,(next adj v).card≤Δ) (branch : 2≤Δ) (scale_pos : 0<2^a*B) (two : 2≤2^a) :
    let D := 32*Nat.clog 2 (2*Δ)
    ∃ p : P, (∑g,((leaves (rearrangedLoad (weight g) (family p)) adj D a B
        (fun v i=>limit g v ((rearrange (family p)).symm i))).card:ℝ)) ≤
      (Fintype.card G:ℝ)*Fintype.card V + 240*(∑g,∑v,∑i,(weight g v i:ℝ))/(2^a*B:ℕ) := by
  let D := 32*Nat.clog 2 (2*Δ)
  let cost (p : P) (g : G) : ℝ := (leaves (rearrangedLoad (weight g) (family p)) adj D a B
    (fun v i=>limit g v ((rearrange (family p)).symm i))).card
  obtain ⟨L,low⟩ := exists_layout_le_average (fun L=>∑g,cost L g)
  refine ⟨L,low.trans ?_⟩
  rw [average_sum]
  calc
    _ ≤ ∑ g,((Fintype.card V:ℝ)+240*(∑ w,∑ i, normalized (weight g) (2^a*B:ℕ) w i)) :=
      Finset.sum_le_sum fun g _=> expected_colonies_family family pairs (weight g) adj a B Δ (limit g) degree branch scale_pos two
    _ = _ := by
      simp only [normalized,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        ←Finset.mul_sum,←Finset.sum_div]
      ring

/-- In particular, the shared layout can be chosen from the whole binary linear group. -/
theorem exists_shared_colonies {G : Type*} [Fintype G] (weight : G → V → Block k → ℕ)
    (adj : V → V → Prop) (a B Δ : ℕ) (limit : ∀ g v i,weight g v i≤B)
    (degree : ∀v,(next adj v).card≤Δ) (branch : 2≤Δ) (scale_pos : 0<2^a*B) (two : 2≤2^a) :
    let D := 32*Nat.clog 2 (2*Δ)
    ∃ L : Layout k, (∑g,((leaves (rearrangedLoad (weight g) L) adj D a B
        (fun v i=>limit g v ((rearrange L).symm i))).card:ℝ)) ≤
      (Fintype.card G:ℝ)*Fintype.card V + 240*(∑g,∑v,∑i,(weight g v i:ℝ))/(2^a*B:ℕ) := by
  let : Nonempty (Layout k) := ⟨LinearEquiv.refl _ _⟩
  exact exists_shared_colonies_family id (fun hj => real_layout_pairs hj) weight adj a B Δ limit degree branch scale_pos two

end
end Hierarchy.DescentColonies

end OAI
