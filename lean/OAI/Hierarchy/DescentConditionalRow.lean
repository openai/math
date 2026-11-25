import OAI.Hierarchy.DescentGLConditionalMean
import OAI.Hierarchy.DescentGLNativeSelection

namespace OAI
/-! # A single Walsh table evaluates the future collision cost of every next row -/

namespace Hierarchy.DescentGL

open scoped Classical BigOperators
noncomputable section

variable {h r : ℕ}
local notation "k" => (h+1)+r

/-- Collision cost at all depths at or beyond the proposed next row. The table
at index `j` counts collisions at depth `h+1+j`. -/
def futureCollisionCost (weights : Fin (r+1) → Nonzero k → ℝ) (L : Layout k) : ℝ :=
  ∑ j, ∑ d : Nonzero k, weights j d *
    (if headRows (Nat.add_le_add_left (Nat.le_of_lt_succ j.isLt) (h+1)) (L d.val)=0
     then 1 else 0)

/-- Aggregate the true tail probabilities on the kernel of the already fixed
rows, and extend by zero to the zero difference. -/
def conditionalRowAggregate (base : Layout k) (weights : Fin (r+1) → Nonzero k → ℝ)
    (x : Bits k) : ℝ :=
  if hx : x ≠ 0 then
    if headRows (show h≤k by omega) (base x)=0 then
      ∑ j, weights j ⟨x,hx⟩ * (((2^(r-j.val)-1 : ℕ) : ℝ) / ((2^r-1 : ℕ) : ℝ))
    else 0
  else 0

/-- The constant coefficient plus the Walsh coefficient, with the common
factor of one half from the kernel indicator. -/
def conditionalRowScore (base : Layout k) (weights : Fin (r+1) → Nonzero k → ℝ)
    (row : Row k) : ℝ :=
  ((∑ x, conditionalRowAggregate base weights x) +
    DescentRowScore.walsh row (conditionalRowAggregate base weights))/2

private theorem next_head_survives (base T : Layout k)
    (agrees : ∀ i<h, layoutRow T i=layoutRow base i) (x : Bits k) :
    (splitRows (h+1) r (T x)).1=0 ↔
      headRows (show h≤k by omega) (base x)=0 ∧
      rowFunctional T ⟨h,by omega⟩ x=0 := by
  have prev (i : Fin h) : T x ⟨i.val,by omega⟩ = base x ⟨i.val,by omega⟩ := by
    have hi : i.val<k := by omega
    simpa only [layoutRow, dite_eq_left hi] using congrFun (agrees i.val i.isLt) x
  rw [rowFunctional_apply]
  constructor
  · intro head
    exact ⟨funext fun i => (prev i).symm.trans (congrFun head i.castSucc),
      congrFun head (Fin.last h)⟩
  · rintro ⟨old, last⟩
    funext l
    refine Fin.lastCases ?_ (fun i => ?_) l
    · exact last
    · exact (prev i).trans (congrFun old i)

private theorem sum_nonzero {n : ℕ} (f : Bits n → ℝ) (hz : f 0=0) :
    (∑ d : Nonzero n, f d.val) = ∑ x, f x := by
  rw [←Finset.sum_subtype (p:=fun d : Bits n => d≠0) (Finset.univ.erase 0) (fun _ => by simp) f]
  simpa only [hz, add_zero] using Finset.sum_erase_add Finset.univ f (Finset.mem_univ 0)

/-- For each feasible row, its Walsh score is the actual completion mean of the
multidepth collision cost. -/
theorem prefixMean_eq_rowScore (base T : Layout k) (weights : Fin (r+1) → Nonzero k → ℝ)
    (agrees : ∀ i<h, layoutRow T i=layoutRow base i) :
    prefixMean (futureCollisionCost weights) T (h+1) =
      conditionalRowScore base weights (rowFunctional T ⟨h,by omega⟩) := by
  let c (j : Fin (r+1)) (L : Layout k) := ∑ d : Nonzero k, weights j d *
    (if headRows (Nat.add_le_add_left (Nat.le_of_lt_succ j.isLt) (h+1)) (L d.val)=0 then 1 else 0)
  let row := rowFunctional T (⟨h,by omega⟩ : Fin k)
  let f (x : Bits k) := if row x=0 then conditionalRowAggregate base weights x else 0
  have one (j : Fin (r+1)) :=
    prefixMean_weighted_collisions (h:=h+1) (Nat.le_of_lt_succ j.isLt) T (weights j)
  change prefixMean (fun L => ∑ j, c j L) T (h+1) = _
  calc
    _ = ∑ j, prefixMean (c j) T (h+1) := by
      simp only [prefixMean_eq_completions]
      rw [Finset.sum_comm, Finset.sum_div]
    _ = ∑ d : Nonzero k, ∑ j : Fin (r+1), weights j d *
        (if (splitRows (h+1) r (T d.val)).1=0 then
          ((2^(r-j.val)-1:ℕ):ℝ) / ((2^r-1:ℕ):ℝ) else 0) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => one j
    _ = ∑ d : Nonzero k, f d.val := by
      apply Finset.sum_congr rfl
      intro d _
      have survives : (splitRows (h+1) r (T d.val)).1=0 ↔
          headRows (show h≤k by omega) (base d.val)=0 ∧ row d.val=0 :=
        next_head_survives base T agrees d.val
      by_cases old : headRows (show h≤k by omega) (base d.val)=0 <;>
        by_cases current : row d.val=0 <;>
        simp [f, survives, conditionalRowAggregate, d.property, old, current]
    _ = ∑ x, f x := sum_nonzero f (by simp [f, conditionalRowAggregate])
    _ = conditionalRowScore base weights row := by
      simpa only [f, conditionalRowScore, Finset.sum_filter] using
        DescentRowScore.kernel_score row (conditionalRowAggregate base weights)

/-- The legal row menu, with its fixed least-index tie break, retains a genuine
invertible completion and does not increase the conditional mean. -/
theorem chosenRow_futureCollisions (base : Layout k) (weights : Fin (r+1) → Nonzero k → ℝ) :
    ∃ L : Layout k, (∀ i<h,layoutRow L i=layoutRow base i) ∧
      rowFunctional L ⟨h,by omega⟩=(rowIndex k).symm
        (chosenIndex (show h<k by omega) base (conditionalRowScore base weights)) ∧
      prefixMean (futureCollisionCost weights) L (h+1) ≤
        prefixMean (futureCollisionCost weights) base h :=
  chosenIndex_completion (by omega) base (futureCollisionCost weights) (conditionalRowScore base weights)
    (fun T agrees => prefixMean_eq_rowScore base T weights agrees)

/-- A fixed collision potential, with one weight table at each possible depth. -/
def allDepthCollisionCost {n : ℕ} (weights : Fin (n+1) → Nonzero n → ℝ) (L : Layout n) : ℝ :=
  ∑ j, ∑ d : Nonzero n, weights j d *
    (if headRows (Nat.le_of_lt_succ j.isLt) (L d.val)=0 then 1 else 0)

private def priorCollisionCost (weights : Fin (k+1) → Nonzero k → ℝ) (L : Layout k) : ℝ :=
  ∑ j : Fin (h+1), ∑ d : Nonzero k, weights (j.castAdd (r+1)) d *
    (if headRows (show j.val≤k by omega) (L d.val)=0 then 1 else 0)

private theorem allDepth_split (weights : Fin (k+1) → Nonzero k → ℝ) (L : Layout k) :
    allDepthCollisionCost weights L = priorCollisionCost weights L +
      futureCollisionCost (fun j => weights (Fin.natAdd (h+1) j)) L :=
  Fin.sum_univ_add (a:=h+1) (b:=r+1) _

private theorem priorCollisionCost_fixed (weights : Fin (k+1) → Nonzero k → ℝ) (base T : Layout k)
    (agrees : ∀ i<h, layoutRow T i=layoutRow base i) :
    priorCollisionCost weights T = priorCollisionCost weights base := by
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro d _
  have head : headRows (show j.val≤k by omega) (T d.val)=headRows (by omega) (base d.val) := by
    funext i
    have hi : i.val<h := by omega
    have full : i.val<k := by omega
    change T d.val ⟨i.val,full⟩ = base d.val ⟨i.val,full⟩
    simpa only [layoutRow,dite_eq_left full] using congrFun (agrees i.val hi) d.val
  rw [head]

private theorem prefixMean_add_fixed {n t : ℕ} (base : Layout n) (fixed extra : Layout n → ℝ)
    (C : ℝ) (same : ∀ T, (∀ i<t, layoutRow T i=layoutRow base i) → fixed T=C) :
    prefixMean (fun T => fixed T+extra T) base t = C+prefixMean extra base t := by
  let s := Finset.univ.filter fun T : Layout n => ∀ i<t,layoutRow T i=layoutRow base i
  have members (L : Layout n) : L∈s ↔ ∀i<t,layoutRow L i=layoutRow base i := by simp [s]
  rw [prefixMean_eq_sum_of_mem _ base s members,prefixMean_eq_sum_of_mem extra base s members]
  have constants : (∑ T∈s,fixed T)=∑ _T∈s,C :=
    Finset.sum_congr rfl fun T hT => same T (Finset.mem_filter.mp hT).2
  have hp : (0:ℝ)<s.card := by
    exact_mod_cast Finset.card_pos.mpr (show s.Nonempty from
      ⟨base,Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _=>rfl⟩⟩)
  rw [Finset.sum_add_distrib, constants, add_div, Finset.sum_const, nsmul_eq_mul,
    mul_div_cancel_left₀ _ hp.ne']

theorem prefixMean_const_add {n t : ℕ} (L : Layout n) (c : ℝ) (f : Layout n → ℝ) :
    prefixMean (fun T => c+f T) L t = c+prefixMean f L t :=
  prefixMean_add_fixed L (fun _=>c) f c (fun _ _ => rfl)

/-- For the same objective at every step, earlier depths contribute a fixed
constant. The selected binary index still uses only the aggregated future table. -/
theorem chosenRow_allCollisions (base : Layout k) (weights : Fin (k+1) → Nonzero k → ℝ) :
    ∃ L : Layout k, (∀ i<h,layoutRow L i=layoutRow base i) ∧
      rowFunctional L ⟨h,by omega⟩=(rowIndex k).symm (chosenIndex (show h<k by omega) base
        (conditionalRowScore base (fun j => weights (Fin.natAdd (h+1) j)))) ∧
      prefixMean (allDepthCollisionCost weights) L (h+1) ≤ prefixMean (allDepthCollisionCost weights) base h := by
  let future := fun j : Fin (r+1) => weights (Fin.natAdd (h+1) j)
  obtain ⟨L,agree,choice,step⟩ := chosenRow_futureCollisions base future
  refine ⟨L,agree,choice,?_⟩
  have splitCost : allDepthCollisionCost weights = fun T => priorCollisionCost weights T +
      futureCollisionCost future T := funext (allDepth_split weights)
  rw [splitCost, prefixMean_add_fixed L _ _ (priorCollisionCost weights base) (fun T rows =>
    priorCollisionCost_fixed weights base T fun i hi =>
      (rows i (by omega)).trans (agree i hi)),
    prefixMean_add_fixed base _ _ (priorCollisionCost weights base) (fun T rows =>
      priorCollisionCost_fixed weights base T rows)]
  exact add_le_add_right step _

private abbrev RowData (n : ℕ) :=
  (Fin (n+1) → Nonzero n → ℝ) → Layout n → ℝ × (Row n → ℝ)

private def splitRowData (a b : ℕ) : RowData ((a+1)+b) := fun weights base =>
  (priorCollisionCost (h:=a) (r:=b) weights base,
    conditionalRowScore base (fun j => weights (Fin.natAdd (a+1) j)))

/-- The fixed contribution from the earlier depths and the Walsh-scored menu
of future depths, at an arbitrary row of an `n`-bit layout. -/
def collisionRowData {n : ℕ} (i : Fin n) :
    (Fin (n+1) → Nonzero n → ℝ) → Layout n → ℝ × (Row n → ℝ) :=
  let e : (i.val+1)+(n-(i.val+1))=n := by omega
  cast (congrArg RowData e) (splitRowData i.val (n-(i.val+1)))

private theorem cast_splitRowData (a b c : ℕ) (bc : b=c) (e : (a+1)+b=(a+1)+c) :
    cast (congrArg RowData e) (splitRowData a b)=splitRowData a c := by
  subst c
  rfl

private theorem collisionRowData_split (a b : ℕ) :
    collisionRowData (⟨a,by omega⟩ : Fin ((a+1)+b)) = splitRowData a b := by
  exact cast_splitRowData a ((a+1)+b-(a+1)) b (by omega) (by omega)

/-- At an explicit row and tail dimension, the score read by the global
layout controller is precisely the fixed-coefficient Walsh row functional. -/
theorem collisionRowData_snd (h r : ℕ) (w : Fin (((h+1)+r)+1) → Nonzero ((h+1)+r) → ℝ)
    (base : Layout ((h+1)+r)) :
    (collisionRowData (⟨h,by omega⟩ : Fin ((h+1)+r)) w base).2 =
      conditionalRowScore base (fun j => w (Fin.natAdd (h+1) j)) := by
  rw [collisionRowData_split]
  rfl

theorem allDepth_prefixMean_score {n : ℕ} (i : Fin n) (weights : Fin (n+1) → Nonzero n → ℝ)
    (base T : Layout n) (agree : ∀ j < i.val, layoutRow T j=layoutRow base j) :
    prefixMean (allDepthCollisionCost weights) T (i.val+1) =
      (collisionRowData i weights base).1 + (collisionRowData i weights base).2 (rowFunctional T i) := by
  obtain ⟨j,hj⟩ := i
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le hj
  simp only at agree ⊢
  rw [collisionRowData_split]
  let future := fun l : Fin (b+1) => weights (Fin.natAdd (j+1) l)
  have splitCost : allDepthCollisionCost weights = fun L => priorCollisionCost weights L +
      futureCollisionCost future L := funext (allDepth_split weights)
  rw [splitCost, prefixMean_add_fixed T _ _ (priorCollisionCost weights base) (fun L rows =>
    priorCollisionCost_fixed weights base L fun l hl => (rows l (by omega)).trans (agree l hl)),
    prefixMean_eq_rowScore base T future agree]; rfl

private theorem chosenIndex_add_constant {n a : ℕ} (ha : a<n) (base : Layout n)
    (c : ℝ) (score : Row n → ℝ) :
    chosenIndex ha base (fun row => c+score row)=chosenIndex ha base score := by
  simp only [chosenIndex, DescentRowScore.nextRow, add_le_add_iff_left]

/-- The actual sequence of Walsh-scored choices yields an invertible layout
whose collision potential is bounded by the average over all binary layouts. -/
theorem chosenRow_collisionTrajectory {n : ℕ} (initial : Layout n)
    (weights : Fin (n+1) → Nonzero n → ℝ) :
    ∃ run : ℕ → Layout n, run 0=initial ∧
      (∀ i : Fin n, (∀ j < i.val,layoutRow (run (i.val+1)) j=layoutRow (run i.val) j) ∧
        rowFunctional (run (i.val+1)) i = (rowIndex n).symm (chosenIndex i.isLt (run i.val)
          (collisionRowData i weights (run i.val)).2) ∧
        prefixMean (allDepthCollisionCost weights) (run (i.val+1)) (i.val+1) ≤
          prefixMean (allDepthCollisionCost weights) (run i.val) i.val) ∧
      allDepthCollisionCost weights (run n) ≤
        (∑ T, allDepthCollisionCost weights T) / Fintype.card (Layout n) := by
  obtain ⟨run,start,steps,bound⟩ := chosen_layout_trajectory initial (allDepthCollisionCost weights)
    (fun i L row => (collisionRowData i weights L).1 + (collisionRowData i weights L).2 row)
    (fun i base T => allDepth_prefixMean_score i weights base T)
  refine ⟨run,start,fun i => ?_,bound⟩
  obtain ⟨agree,choice,decrease⟩ := steps i
  exact ⟨agree, by simpa only [chosenIndex_add_constant] using choice, decrease⟩

end
end Hierarchy.DescentGL

end OAI
