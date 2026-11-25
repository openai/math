import OAI.Hierarchy.FactorBuckets
import OAI.Hierarchy.RoundRobin

namespace OAI
/-! # Simultaneous allocation of the work, pairs and advice of the trace factors -/

namespace Hierarchy.FactorAllocation

open scoped BigOperators

abbrev Key (w d : ℕ) := Fin d → Fin (20*(w+1)+2)

/-- The same resource class is used for every coordinate of a factor. -/
def key {α : Type*} {d : ℕ} (w : ℕ) (cost : α → Fin d → ℕ) (x : α) : Key w d :=
  fun j => FactorBucket.label w (cost x j)

def group {α κ : Type*} [DecidableEq κ] (tag : α → κ) (items : List α) (g : κ) : List α :=
  items.filter (fun a => decide (tag a = g))

private noncomputable def value {α : Type*} (c : α → ℝ) (items : List α) (i : ℕ) :=
  ((items[i]?).map c).getD 0

theorem sum_group {α κ : Type*} [Fintype κ] [DecidableEq κ] (tag : α → κ) (items : List α) (c : α → ℝ) :
    (∑ g, ((group tag items g).map c).sum) = (items.map c).sum := by
  classical
  induction items with
  | nil => simp [group]
  | cons a xs ih =>
    have step (g : κ) : ((group tag (a::xs) g).map c).sum =
        (if tag a=g then c a else 0) + ((group tag xs g).map c).sum := by
      by_cases h : tag a = g <;> simp [group,h]
    simp only [step,Finset.sum_add_distrib,ih,List.map_cons,List.sum_cons]
    simp

private theorem sum_value {α : Type*} (c : α → ℝ) (items : List α) :
    (∑ i∈Finset.range items.length, value c items i)=(items.map c).sum := by
  induction items with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simpa [value, add_comm] using congrArg (· + c a) ih

/-- The load at a tick sums the original factors at their round-robin positions.
The grouping and positions depend only on the list and its integral resource vectors. -/
noncomputable def tickLoad {α : Type*} {d T : ℕ} (w : ℕ) (cost : α → Fin d → ℕ)
    (items : List α) (j : Fin d) (tick : Fin T) : ℝ :=
  ∑ g : Key w d, let xs := group (key w cost) items g
                  ∑ i∈RoundRobin.selected xs.length T tick, value (fun a => (cost a j : ℝ)) xs i

/-- Aggregating every tick accounts for every original factor, including repeated
resource vectors or repeated values in the original list. -/
theorem sum_tickLoad {α : Type*} {d T w : ℕ} (ht : 0<T) (cost : α → Fin d → ℕ)
    (items : List α) (j : Fin d) :
    (∑ t : Fin T, tickLoad w cost items j t)=(items.map (fun a=>(cost a j : ℝ))).sum := by
  classical
  unfold tickLoad
  rw [Finset.sum_comm]
  simp_rw [RoundRobin.sum_selected _ _ ht, sum_value]
  exact sum_group _ _ _

/-- For each coordinate the load differs from its multiplicatively enlarged
mean by at most one maximum item per bucket. -/
theorem tickLoad_bounds {α : Type*} {d T w : ℕ} (cost : α → Fin d → ℕ)
    (items : List α) (cap : ℕ) (width : ∀ a∈items, ∀ j, cost a j≤2^w)
    (bounded : ∀ a∈items, ∀ j, cost a j≤cap) (j : Fin d) (tick : Fin T) :
    let mean := (items.map (fun x => (cost x j : ℝ))).sum / T
    let classes := (20*((w:ℝ)+1)+2)^d
    mean/(21/20) - classes*cap ≤ tickLoad w cost items j tick ∧
      tickLoad w cost items j tick ≤ (21/20)*mean + classes*((21/20)*cap) := by
  classical
  let c : α → ℝ := fun a => cost a j
  let xs (g : Key w d) := group (key w cost) items g
  let lo (g : Key w d) := min (FactorBucket.lower w (g j)) (cap:ℝ)
  have nonneg (g : Key w d) : 0≤lo g := le_min (FactorBucket.lower_nonneg _ _) (by positivity)
  have span (g : Key w d) (i : ℕ) (hi : i<(xs g).length) :
      lo g ≤ value c (xs g) i ∧ value c (xs g) i ≤ (21/20:ℝ)*lo g := by
    let a := (xs g)[i]
    have member := List.getElem_mem (l:=xs g) hi
    have split : a∈items ∧ key w cost a=g := by
      change a ∈ List.filter (fun x => decide (key w cost x=g)) items at member
      simpa only [List.mem_filter, decide_eq_true_eq] using member
    have read : value c (xs g) i=c a := by simp [value,hi,a]
    rw [read]
    have hc := FactorBucket.bounds w (cost a j) (width a split.1 j)
    have gj : FactorBucket.label w (cost a j)=g j := congrFun split.2 j
    rw [gj] at hc
    have capBound : c a ≤ (cap:ℝ) := by
      dsimp only [c]
      exact_mod_cast bounded a split.1 j
    refine ⟨(min_le_left ..).trans hc.1,?_⟩
    dsimp only [lo]
    rcases le_total (FactorBucket.lower w (g j)) (cap:ℝ) with first|last
    · rw [min_eq_left first];exact hc.2
    · rw [min_eq_right last];linarith [show 0≤(cap:ℝ) by positivity]
  let load (g : Key w d) := ∑ i∈RoundRobin.selected (xs g).length T tick, value c (xs g) i
  let total (g : Key w d) := ((xs g).map c).sum
  have single (g : Key w d) :
      total g/((T:ℝ)*(21/20)) - cap ≤ load g ∧
      load g ≤ (21/20)*(total g/T)+(21/20)*(cap:ℝ) := by
    have h := RoundRobin.load_bounds (xs g).length T tick (value c (xs g)) (lo g) (21/20)
      (nonneg g) (by norm_num) (span g)
    rw [sum_value] at h
    have low : lo g ≤ (cap:ℝ) := min_le_right ..
    exact ⟨(sub_le_sub_left low _).trans h.1,
      h.2.trans (add_le_add_right (mul_le_mul_of_nonneg_left low (by norm_num : (0:ℝ)≤21/20)) _)⟩
  have sumL := Finset.sum_le_sum (s:=Finset.univ) (fun g _=>(single g).1)
  have sumH := Finset.sum_le_sum (s:=Finset.univ) (fun g _=>(single g).2)
  have joined : (∑ g, total g)=(items.map c).sum := sum_group (key w cost) items c
  have num : ((Fintype.card (Key w d)):ℝ)=(20*((w:ℝ)+1)+2)^d := by
    simp [Key]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.sum_div,
    ←Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,joined,num] at sumL sumH
  have same : (∑ g, load g) = tickLoad w cost items j tick := by rfl
  rw [same] at sumL sumH
  dsimp only
  constructor
  · rw [div_div]
    exact sumL
  · simpa only [mul_left_comm (21/20 : ℝ)] using sumH

end Hierarchy.FactorAllocation

end OAI
