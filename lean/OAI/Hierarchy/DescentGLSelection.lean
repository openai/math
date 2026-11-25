import OAI.Hierarchy.DescentGLFiber
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI
/-! # Conditional expectation along the rows of an invertible binary layout -/

namespace Hierarchy.DescentGL
open scoped Classical BigOperators
noncomputable section

private def meanOn {A : Type*} (f : A → ℝ) (s : Finset A) :=
  (∑ x ∈ s,f x) / s.card

/-- Splitting a finite completion ensemble by its next row leaves at least one
nonempty child whose average potential does not exceed the parent's. -/
private theorem choose_fiber {A B : Type*} (s : Finset A) (hs : s.Nonempty)
    (row : A → B) (f : A → ℝ) :
    ∃ p ∈ s, meanOn f (s.filter fun x => row x = row p) ≤ meanOn f s := by
  let C (b : B) := s.filter fun x => row x = b
  have partition := Finset.sum_fiberwise_of_maps_to
    (s := s) (t := s.image row) (fun _ hx => Finset.mem_image_of_mem row hx) f
  have counts : (∑ b ∈ s.image row, ((C b).card : ℝ)) = s.card := by
    exact_mod_cast (Finset.card_eq_sum_card_image row s).symm
  have sPos : (0:ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  by_contra! worse
  have hbad (b : B) (hb : b ∈ s.image row) :
      meanOn f s * ((C b).card : ℝ) < ∑ x ∈ C b,f x := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb
    have subsetPos : (C (row x)).Nonempty := ⟨x,Finset.mem_filter.mpr ⟨hx,rfl⟩⟩
    exact (lt_div_iff₀ (by exact_mod_cast Finset.card_pos.mpr subsetPos :
      (0:ℝ)<(C (row x)).card)).mp (worse x hx)
  have hsum := Finset.sum_lt_sum_of_nonempty (hs.image row) hbad
  rw [←Finset.mul_sum, counts] at hsum
  change meanOn f s * (s.card : ℝ) < ∑ b ∈ s.image row, ∑ x ∈ s.filter (fun u=>row u=b), f x at hsum
  rw [partition, meanOn, div_mul_cancel₀ _ sPos.ne'] at hsum
  exact (lt_irrefl _ hsum)

private def completionsOn {A B : Type*} [Fintype A] (rows : A → ℕ → B) (p : A) (h : ℕ) :=
  Finset.univ.filter fun x => ∀ i<h, rows x i = rows p i

private theorem mem_completionsOn {A B : Type*} [Fintype A] {rows : A → ℕ → B} {p q : A} {h : ℕ} :
    q ∈ completionsOn rows p h ↔ ∀ i<h,rows q i=rows p i := by
  simp [completionsOn]

private theorem same_completions {A B : Type*} [Fintype A] {rows : A → ℕ → B} {p q : A} {h j : ℕ}
    (hq : q ∈ completionsOn rows p h) (hj : j≤h) :
    completionsOn rows q j=completionsOn rows p j := by
  ext x
  simp only [mem_completionsOn]
  constructor
  · intro hx i hi
    exact (hx i hi).trans ((mem_completionsOn.mp hq) i (hi.trans_le hj))
  · intro hx i hi
    exact (hx i hi).trans ((mem_completionsOn.mp hq) i (hi.trans_le hj)).symm

private theorem next_completions {A B : Type*} [Fintype A] {rows : A → ℕ → B} {p q : A} {h : ℕ}
    (hq : q ∈ completionsOn rows p h) :
    (completionsOn rows p h).filter (fun x=>rows x h=rows q h) = completionsOn rows q (h+1) := by
  rw [← same_completions hq (le_refl h)]
  ext x
  simp only [Finset.mem_filter, mem_completionsOn]
  constructor
  · intro pair i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with lt|rfl
    · exact pair.1 _ lt
    · exact pair.2
  · intro allRows
    exact ⟨fun i hi=>allRows i (by omega),allRows h (by omega)⟩

private theorem prefix_path {A B : Type*} [Fintype A] [Nonempty A] (rows : A → ℕ → B) (f : A → ℝ) (n : ℕ) :
    ∃ p, ∀ i<n,meanOn f (completionsOn rows p (i+1)) ≤ meanOn f (completionsOn rows p i) := by
  induction n with
  | zero => exact ⟨Classical.arbitrary _,fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
  | succ n ih =>
    obtain ⟨p,prev⟩ := ih
    have hp : p ∈ completionsOn rows p n := mem_completionsOn.mpr (fun _ _=>rfl)
    obtain ⟨q,hq,next⟩ := choose_fiber _ ⟨p,hp⟩ (fun x=>rows x n) f
    refine ⟨q, fun i hi => ?_⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with lt|rfl
    · rw [same_completions hq (Nat.succ_le_of_lt lt), same_completions hq lt.le]
      exact prev i lt
    · rw [same_completions hq (le_refl _), ← next_completions hq]
      exact next

def layoutRow {k : ℕ} (L : Layout k) (i : ℕ) (x : Bits k) : ZMod 2 :=
  if hi : i<k then L x ⟨i,hi⟩ else 0

/-- The average over all invertible completions agreeing on the first `h` rows.
The row function here is the complete linear functional on the input space. -/
def prefixMean {k : ℕ} (cost : Layout k → ℝ) (L : Layout k) (h : ℕ) : ℝ :=
  meanOn cost (completionsOn layoutRow L h)

/-- Compute the mean over any finite set with the specified rows. This allows
its construction to use the decidability instance natural to its application. -/
theorem prefixMean_eq_sum_of_mem {k h : ℕ} (cost : Layout k → ℝ) (base : Layout k)
    (s : Finset (Layout k)) (members : ∀ L, L∈s ↔ ∀ i<h,layoutRow L i=layoutRow base i) :
    prefixMean cost base h=(∑ L∈s,cost L)/(s.card : ℝ) := by
  have eqn : completionsOn layoutRow base h=s :=
    Finset.ext fun L => mem_completionsOn.trans (members L).symm
  change meanOn cost (completionsOn layoutRow base h)=_
  rw [eqn]; rfl

/-- A controller which picks a minimizing next row never increases the
conditional mean, independently of how it breaks ties. -/
theorem minimizing_next_row {k h : ℕ} (cost : Layout k → ℝ) (p chosen : Layout k)
    (best : ∀ T : Layout k, (∀ i<h, layoutRow T i=layoutRow p i) →
      prefixMean cost chosen (h+1) ≤ prefixMean cost T (h+1)) :
    prefixMean cost chosen (h+1) ≤ prefixMean cost p h := by
  have hp : p ∈ completionsOn layoutRow p h := mem_completionsOn.mpr (fun _ _=>rfl)
  obtain ⟨q,hq,next⟩ := choose_fiber _ ⟨p,hp⟩ (fun x=>layoutRow x h) cost
  apply (best q (mem_completionsOn.mp hq)).trans
  rw [next_completions hq] at next
  exact next

theorem prefixMean_zero {k : ℕ} (cost : Layout k → ℝ) (L : Layout k) :
    prefixMean cost L 0 = (∑ T, cost T) / Fintype.card (Layout k) := by
  simp [prefixMean, meanOn, completionsOn]

theorem prefixMean_full {k : ℕ} (cost : Layout k → ℝ) (L : Layout k) :
    prefixMean cost L k = cost L := by
  have unique : completionsOn layoutRow L k = {L} := by
    ext T
    simp only [mem_completionsOn,Finset.mem_singleton]
    constructor
    · intro same
      apply LinearEquiv.ext
      intro x
      funext i
      simpa [layoutRow,i.isLt] using congrFun (same i.val i.isLt) x
    · rintro rfl i hi
      rfl
  change meanOn cost (completionsOn layoutRow L k) = _
  simp [unique, meanOn]

/-- The successive conditional expectations form a nonincreasing path all
the way to an invertible layout with its rows fully specified. -/
theorem exists_conditional_layout (k : ℕ) (cost : Layout k → ℝ) :
    ∃ L : Layout k, ∀ h<k, prefixMean cost L (h+1) ≤ prefixMean cost L h := by
  let : Nonempty (Layout k) := ⟨LinearEquiv.refl _ _⟩
  exact prefix_path _ _ k

/-- Telescoping the conditional means bounds the score of the selected
complete matrix by the original uniform average. -/
theorem score_le_average_of_rows {k : ℕ} (cost : Layout k → ℝ) (L : Layout k)
    (steps : ∀ h<k, prefixMean cost L (h+1) ≤ prefixMean cost L h) :
    cost L ≤ (∑ T, cost T) / Fintype.card (Layout k) := by
  have chain (h : ℕ) (hh : h≤k) : prefixMean cost L h ≤ prefixMean cost L 0 := by
    induction h with
    | zero => exact le_rfl
    | succ h ih => exact (steps h hh).trans (ih (Nat.le_of_lt hh))
  simpa only [prefixMean_zero,prefixMean_full] using chain k le_rfl


end
end Hierarchy.DescentGL

end OAI
