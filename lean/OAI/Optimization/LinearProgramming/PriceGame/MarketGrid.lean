import OAI.Optimization.LinearProgramming.PriceGame.MarketBinary
import OAI.Optimization.LinearProgramming.PriceGame.MarketPotentialsCost
import Mathlib.Data.Rat.Floor

/-! Integer-grid Bellman witnesses. Numeric decisions in the inner loop use signed bit circuits
on the scaled score and the cached path length. Vertex and edge indices follow input order. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Grid

open Quiver Potentials

/-- The integer coordinate of an exactly representable price, in units of `1 / D`. -/
def coordinate (D : ℕ) (q : ℚ) : ℤ := ⌊(D : ℚ)*q⌋

theorem coordinate_cast {D : ℕ} {q : ℚ} (h : NumberBounds.OnGrid D q) :
    ((coordinate D q : ℤ) : ℚ) = (D : ℚ)*q := by
  obtain ⟨z, hz⟩ := h
  simp [coordinate, hz]

theorem coordinate_add {D : ℕ} {q r : ℚ} (hq : NumberBounds.OnGrid D q)
    (hr : NumberBounds.OnGrid D r) : coordinate D (q+r) = coordinate D q + coordinate D r := by
  apply (Int.cast_injective (α := ℚ))
  rw [Int.cast_add, coordinate_cast hq, coordinate_cast hr, coordinate_cast (hq.add hr), mul_add]

private theorem coordinate_lt {D : ℕ} (hd : 0 < D) {q r : ℚ} (hq : NumberBounds.OnGrid D q)
    (hr : NumberBounds.OnGrid D r) : coordinate D q < coordinate D r ↔ q < r := by
  have hD : (0 : ℚ) < D := by exact_mod_cast hd
  exact (Int.cast_lt (R := ℚ)).symm.trans (by rw [coordinate_cast hq, coordinate_cast hr,
    mul_lt_mul_iff_of_pos_left hD])

/-- A single width covers every signed score and every nonnegative path-length tie breaker. -/
def magnitude (D C R K : ℕ) := max K (D*(K*C + R))

variable {V : Type*} [Quiver V]

structure WordPlan (W : ℕ) (a : V) where
  finish : V
  path : Path a finish
  score : BitVec W
  hops : BitVec W

namespace WordPlan
variable {W : ℕ} {a b : V}

def stop (terminal : V → BitVec W) (a : V) : WordPlan W a :=
  ⟨a, .nil, terminal a, BitVec.ofInt W 0⟩

/-- Two ripple-carry additions update the stored score and length directly. -/
def prepend (edge : a ⟶ b) (cost : BitVec W) (p : WordPlan W b) : WordPlan W a × ℕ :=
  let s := Binary.add cost p.score
  let h := Binary.add (BitVec.ofInt W 1) p.hops
  (⟨p.finish, edge.toPath.comp p.path, s.1, h.1⟩, s.2+h.2)

def less (p q : WordPlan W a) : Bool × ℕ :=
  let xy := Binary.signedLT p.score q.score
  let yx := Binary.signedLT q.score p.score
  let shorter := Binary.signedLT q.hops p.hops
  (xy.1 || (!yx.1 && shorter.1), xy.2+yx.2+shorter.2+3)

theorem prepend_gates (edge : a ⟶ b) (cost : BitVec W) (p : WordPlan W b) :
    (prepend edge cost p).2 = 10*W := by simp [prepend, Binary.add_spec]; omega

theorem less_gates (p q : WordPlan W a) : (less p q).2 = 15*W+9 := by
  simp [less, Binary.signedLT_spec]
  omega

/-- Compare in the supplied enumeration order, keeping the earliest tied plan. -/
def choose (first : WordPlan W a) : List (WordPlan W a) → WordPlan W a × ℕ
  | [] => (first,0)
  | second :: others =>
    let tail := choose second others
    let cmp := less first tail.1
    (if cmp.1 then tail.1 else first, tail.2 + cmp.2)

theorem choose_gates (first : WordPlan W a) (xs : List (WordPlan W a)) :
    (choose first xs).2 = xs.length*(15*W+9) := by
  induction xs generalizing first <;> simp [choose, *, less_gates, Nat.succ_mul]

end WordPlan

variable (w : ∀ {a b : V}, (a ⟶ b) → ℚ) (r : V → ℚ)

def encode (D B : ℕ) {a : V} (p : Plan w r a) : WordPlan (Binary.widthFor B) a :=
  ⟨p.finish, p.path, BitVec.ofInt _ (coordinate D p.total), BitVec.ofInt _ p.steps⟩

/-- All words reachable in a bounded horizon encode exact integers. -/
structure Fits (D B : ℕ) {a : V} (p : Plan w r a) : Prop where
  grid : NumberBounds.OnGrid D p.total
  score : |coordinate D p.total| ≤ (B : ℤ)
  hops : p.steps ≤ B

private def referenceKey {a : V} (p : Plan w r a) : ℚ ×ₗ OrderDual ℕ :=
  toLex (p.total, p.steps)

private theorem reference_lt {a : V} (p q : Plan w r a) :
    referenceKey w r p < referenceKey w r q ↔ p.total < q.total ∨ p.total = q.total ∧ q.steps < p.steps :=
  Prod.Lex.toLex_lt_toLex

private theorem pick_argmax {a : V} (p : Plan w r a) (rest : List (Plan w r a)) :
    (p::rest).argmax (referenceKey w r) = some (Plan.pick p rest) := by
  change (p::rest).argmax (referenceKey w r) = some (((p::rest).argmax (referenceKey w r)).getD p)
  cases h : (p::rest).argmax (referenceKey w r) with
  | none => simp at h
  | some q => rfl

theorem compare_encode {D B : ℕ} (hD : 0 < D) {a : V} {p q : Plan w r a}
    (hp : Fits w r D B p) (hq : Fits w r D B q) :
    (WordPlan.less (encode w r D B p) (encode w r D B q)).1 =
      decide (referenceKey w r p < referenceKey w r q) := by
  have hsp : |(p.steps : ℤ)| ≤ (B : ℤ) := by simpa using (show (p.steps : ℤ) ≤ B by exact_mod_cast hp.hops)
  have hsq : |(q.steps : ℤ)| ≤ (B : ℤ) := by simpa using (show (q.steps : ℤ) ≤ B by exact_mod_cast hq.hops)
  simp only [WordPlan.less, encode, Binary.compare_word hp.score hq.score,
    Binary.compare_word hq.score hp.score, Binary.compare_word hsq hsp, Int.ofNat_lt,
    coordinate_lt hD hp.grid hq.grid, coordinate_lt hD hq.grid hp.grid, reference_lt]
  by_cases h : p.total < q.total
  · simp [h]
  · by_cases eq : p.total = q.total
    · simp [eq]
    · have rev : q.total < p.total := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm eq)
      simp [h, eq, rev]

theorem choose_encode {D B : ℕ} (hD : 0 < D) {a : V} (first : Plan w r a) (rest : List (Plan w r a))
    (ok : ∀ p ∈ first::rest, Fits w r D B p) :
    (WordPlan.choose (encode w r D B first) (rest.map (encode w r D B))).1 =
      encode w r D B (Plan.pick first rest) := by
  induction rest generalizing first with
  | nil => simp [WordPlan.choose, Plan.pick]
  | cons second rest ih =>
    let tail := Plan.pick second rest
    have htail : tail ∈ second :: rest := List.argmax_mem (pick_argmax w r second rest)
    have hcompare := compare_encode w r hD (ok first List.mem_cons_self)
      (ok tail (List.mem_cons_of_mem _ htail))
    have hchoose : Plan.pick first (second::rest) =
        if referenceKey w r first < referenceKey w r tail then tail else first := by
      change ((first::second::rest).argmax (referenceKey w r)).getD first = _
      rw [List.argmax_cons, pick_argmax w r second rest]
      change (if referenceKey w r first < referenceKey w r tail then some tail else some first).getD first = _
      split <;> rfl
    simp only [List.map_cons, WordPlan.choose]
    rw [ih second (fun p hp => ok p (List.mem_cons_of_mem _ hp)), hcompare, hchoose]
    by_cases h : referenceKey w r first < referenceKey w r tail
    · simp only [h, decide_true, ite_true]; rfl
    · simp only [h, decide_false, Bool.false_eq_true, ite_false]

theorem prepend_encode {D B : ℕ} {a b : V} (e : a ⟶ b) (p : Plan w r b)
    (he : NumberBounds.OnGrid D (w e)) (hp : NumberBounds.OnGrid D p.total) :
    (WordPlan.prepend e (BitVec.ofInt _ (coordinate D (w e))) (encode w r D B p)).1 =
      encode w r D B (Plan.prepend e p) := by
  simp only [WordPlan.prepend, encode, Plan.prepend, Binary.add_word, coordinate_add he hp, Nat.cast_add, Nat.cast_one]


theorem fits_of_steps_le (D C R K : ℕ)
    (edgegrid : ∀ {i j : V} (e : i ⟶ j), NumberBounds.OnGrid D (w e))
    (endgrid : ∀ j, NumberBounds.OnGrid D (r j))
    (hedge : ∀ {i j : V} (e : i ⟶ j), |w e| ≤ (C : ℚ)) (hend : ∀ i, |r i| ≤ (R : ℚ))
    {a : V} (p : Plan w r a) (hp : p.steps ≤ K) : Fits w r D (magnitude D C R K) p := by
  have hL : p.path.length ≤ K := p.steps_spec ▸ hp
  have hg : NumberBounds.OnGrid D p.total := p.total_spec ▸
    NumberBounds.OnGrid.add (weight_denominator w D edgegrid p.path) (endgrid p.finish)
  have hscore : |p.total| ≤ (K*C+R : ℕ) := by
    rw [p.total_spec, Nat.cast_add, Nat.cast_mul]
    have h₁ := abs_weight_le w (C : ℚ) hedge p.path
    have h₂ : (p.path.length : ℚ) * C ≤ (K : ℚ) * C := mul_le_mul_of_nonneg_right
      (by exact_mod_cast hL) (Nat.cast_nonneg _)
    exact (abs_add_le _ _).trans (add_le_add (h₁.trans h₂) (hend _))
  have hAbs : |(coordinate D p.total : ℚ)| ≤ ((D*(K*C+R) : ℕ) : ℚ) := by
    rw [coordinate_cast hg, abs_mul, Nat.cast_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℚ) D)]
    exact mul_le_mul_of_nonneg_left hscore (Nat.cast_nonneg _)
  have hs : |coordinate D p.total| ≤ (D*(K*C+R) : ℕ) := by exact_mod_cast hAbs
  exact ⟨hg, hs.trans (by exact_mod_cast (le_max_right K (D*(K*C+R)))), hp.trans (le_max_left ..)⟩

variable {n : ℕ} (index : V ≃ Fin n)
variable {W : ℕ} (costWords : ∀ {a b : V}, (a ⟶ b) → BitVec W) (rewardWords : V → BitVec W)
variable (out : (a : V) → List (Σ j : V, a ⟶ j))

def makeRow (prev : (v : V) → WordPlan W v) (a : V) : WordPlan W a × ℕ :=
  let candidates := (out a).map (fun je => WordPlan.prepend je.2 (costWords je.2) (prev je.1))
  let selection := WordPlan.choose (WordPlan.stop rewardWords a) (candidates.map Prod.fst)
  (selection.1, selection.2 + (candidates.map Prod.snd).sum)

theorem makeRow_gates (prev : (v : V) → WordPlan W v) (a : V) :
    (makeRow costWords rewardWords out prev a).2 = (out a).length*(25*W+9) := by
  have per (xs : List (Σ j : V, a ⟶ j)) :
      ((xs.map (fun je => WordPlan.prepend je.2 (costWords je.2) (prev je.1))).map Prod.snd).sum =
      xs.length*(10*W) := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, WordPlan.prepend_gates, List.length_cons, Nat.succ_mul]
      omega
  simp only [makeRow, WordPlan.choose_gates, List.length_map, per]
  ring

/-- The row and total gate counts are stored alongside the table. The incoming integer
weights and rewards can be materialized before the first iteration. -/
structure WordRun (index : V ≃ Fin n) (W : ℕ) where
  layer : Layer (fun j => WordPlan W (index.symm j) × ℕ)
  gates : ℕ

def execute : ℕ → WordRun index W
  | 0 => ⟨Layer.tabulate index (fun a => (WordPlan.stop rewardWords a,0)),0⟩
  | k+1 =>
    let previous := execute k
    let get := fun a => (Layer.lookup (T := fun v => WordPlan W v × ℕ) index previous.layer a).1
    let layer := Layer.tabulate index (makeRow costWords rewardWords out get)
    ⟨layer, previous.gates + ∑ j : Fin n, (layer.get j).2⟩

def result (k : ℕ) (a : V) : WordPlan W a :=
  (Layer.lookup (T := fun v => WordPlan W v × ℕ) index (execute index costWords rewardWords out k).layer a).1

theorem total_gates (k : ℕ) :
    (execute index costWords rewardWords out k).gates =
      k * (∑ j : Fin n, (out (index.symm j)).length) * (25*W+9) := by
  induction k with
  | zero => simp [execute]
  | succ k ih =>
    simp only [execute, Layer.tabulate, Layer.get_ofFn, makeRow_gates, ih]
    rw [← Finset.sum_mul]
    ring

/-- Explicit positive-denominator conversion of the original reduced rational input. -/
def scaleInput (D : ℕ) (q : ℚ) : ℤ := q.num * (D/q.den : ℕ)

theorem scaleInput_eq {D : ℕ} (hD : 0 < D) {q : ℚ} (hg : NumberBounds.OnGrid D q) :
    scaleInput D q = coordinate D q := by
  have hdiv := (NumberBounds.grid_iff_den_dvd hD q).mp hg
  have hfactor : ((D/q.den : ℕ) : ℚ) * q.den = D := by exact_mod_cast Nat.div_mul_cancel hdiv
  have hnum : (q.num : ℚ) = q*q.den := (div_eq_iff (Nat.cast_ne_zero.mpr q.den_ne_zero)).mp q.num_div_den
  apply (Int.cast_injective (α := ℚ))
  simp only [scaleInput, Int.cast_mul, Int.cast_natCast, coordinate_cast hg, hnum]
  rw [← hfactor]
  ring

theorem makeRow_encode (D C R K : ℕ) (hD : 0 < D)
    (edgegrid : ∀ {i j : V} (e : i ⟶ j), NumberBounds.OnGrid D (w e))
    (endgrid : ∀ j, NumberBounds.OnGrid D (r j))
    (hedge : ∀ {i j : V} (e : i ⟶ j), |w e| ≤ (C : ℚ)) (hend : ∀ i, |r i| ≤ (R : ℚ))
    (prev : (i : V) → Plan w r i) (hprev : ∀ i, (prev i).steps < K) (a : V) :
    let B := magnitude D C R K
    (makeRow (fun e => BitVec.ofInt (Binary.widthFor B) (scaleInput D (w e)))
      (fun j => BitVec.ofInt _ (scaleInput D (r j))) out
      (fun j => encode w r D B (prev j)) a).1 =
    encode w r D B (Plan.pick (Plan.stop w r a) ((out a).map (fun je => Plan.prepend je.2 (prev je.1)))) := by
  dsimp only
  let B := magnitude D C R K
  let xs := (out a).map (fun je => Plan.prepend je.2 (prev je.1))
  let start := Plan.stop w r a
  have hfit (p : Plan w r a) (h : p ∈ start::xs) : Fits w r D B p := by
    apply fits_of_steps_le w r D C R K edgegrid endgrid hedge hend
    rcases List.mem_cons.mp h with heq | heq
    · subst p; simp [start, Plan.stop]
    · obtain ⟨⟨j,e⟩,_,rfl⟩ := List.mem_map.mp heq
      change 1 + (prev j).steps ≤ K
      have := hprev j
      omega
  have hgrid (j : V) : NumberBounds.OnGrid D (prev j).total :=
    (fits_of_steps_le w r D C R K edgegrid endgrid hedge hend (prev j) (hprev j).le).grid
  have hbase : WordPlan.stop (fun j => BitVec.ofInt (Binary.widthFor B) (scaleInput D (r j))) a =
      encode w r D B start := by simp [WordPlan.stop, encode, start, Plan.stop, scaleInput_eq hD (endgrid a)]
  have hmap : (((out a).map fun je => WordPlan.prepend je.2
      (BitVec.ofInt (Binary.widthFor B) (scaleInput D (w je.2)))
      (encode w r D B (prev je.1))).map Prod.fst) = xs.map (encode w r D B) := by
    simp only [xs, List.map_map]
    apply List.map_congr_left
    intro je _
    simp only [Function.comp_apply, scaleInput_eq hD (edgegrid je.2)]
    exact prepend_encode w r je.2 (prev je.1) (edgegrid je.2) (hgrid je.1)
  change (WordPlan.choose _ _).1 = _
  rw [hbase, hmap]
  exact choose_encode w r hD start xs hfit

/-- The word machine returns the identical route, target, and tie length selected by the rational
Bellman table. Its score decodes to the exact integer grid coordinate. -/
theorem execute_matches (D C R K : ℕ) (hD : 0 < D)
    (edgegrid : ∀ {i j : V} (e : i ⟶ j), NumberBounds.OnGrid D (w e))
    (endgrid : ∀ j, NumberBounds.OnGrid D (r j))
    (hedge : ∀ {i j : V} (e : i ⟶ j), |w e| ≤ (C : ℚ)) (hend : ∀ i, |r i| ≤ (R : ℚ))
    (k : ℕ) (hk : k ≤ K) (a : V) :
    let B := magnitude D C R K
    result index (fun e => BitVec.ofInt (Binary.widthFor B) (scaleInput D (w e)))
      (fun j => BitVec.ofInt _ (scaleInput D (r j))) out k a =
    encode w r D B (Layer.lookup index (plans index w r out k) a) := by
  dsimp only
  induction k generalizing a with
  | zero =>
    simp only [result, execute, plans, Layer.lookup_tabulate]
    change WordPlan.stop _ a = encode w r D _ (Plan.stop w r a)
    simp only [WordPlan.stop, encode, Plan.stop, scaleInput_eq hD (endgrid a), Nat.cast_zero]
  | succ k ih =>
    simp only [result, execute, Layer.lookup_tabulate, plans]
    have prevEq (j : V) := ih (Nat.le_of_succ_le hk) j
    let B := magnitude D C R K
    have hprev : ∀ j, (Layer.lookup index (plans index w r out k) j).steps < K :=
      fun j => (plans_steps_le index w r out k j).trans_lt (by omega)
    have hm := makeRow_encode w r out D C R K hD edgegrid endgrid hedge hend
      (fun j => Layer.lookup index (plans index w r out k) j) hprev a
    change (makeRow _ _ out (fun j => result index _ _ out k j) a).1 = _
    simp_rw [prevEq]
    exact hm

end Grid
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
