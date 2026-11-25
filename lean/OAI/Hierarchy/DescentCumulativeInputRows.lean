import OAI.Hierarchy.DescentInputTerminals
import OAI.Hierarchy.DescentSparseWordOrder
import Mathlib.Algebra.Order.Floor.Semifield

namespace OAI
/-! # Ordered whole-item row selection by weighted prefix address -/

namespace Hierarchy.DescentBaseProfile.Cumulative
open scoped BigOperators Classical
noncomputable section
variable {I : Type*} [Fintype I] {N Y : ℕ} [NeZero Y] (id : I↪Fin N) (wt : I→ℝ)

def prior (i : I) := ∑j∈DescentOrderedWords.before id i,wt j

/-- A zero-width trailing item is assigned the last real row. -/
def row (S : ℝ) (i : I) : Fin Y :=
  ⟨min ⌊(Y:ℝ)*prior id wt i/(2*S)⌋₊ (Y-1),
    lt_of_le_of_lt (min_le_right _ _) (by have := Nat.pos_of_ne_zero (NeZero.ne Y);omega)⟩

private theorem endpoint (pos : ∀i,0≤wt i) (i : I) : prior id wt i+wt i≤∑j,wt j := by
  have absent : i∉DescentOrderedWords.before id i := by simp [DescentOrderedWords.before]
  calc prior id wt i+wt i=∑v∈insert i (DescentOrderedWords.before id i),wt v := by
         rw [prior,Finset.sum_insert absent,add_comm]
       _≤_ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _=>pos v)

private theorem bracket {S : ℝ} (hS : 0<S) (pos : ∀i,0≤wt i) (full : ∑j,wt j≤2*S)
    {i : I} (live : 0<wt i) :
    (((row (Y:=Y) id wt S i).val:ℝ)*(2*S)≤Y*prior id wt i) ∧
    (Y*prior id wt i<(((row (Y:=Y) id wt S i).val:ℝ)+1)*(2*S)) := by
  have hy : (0:ℝ)<Y := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Y)
  have stop := (endpoint id wt pos i).trans full
  have pr : 0≤prior id wt i := Finset.sum_nonneg fun j _=>pos j
  let x := (Y:ℝ)*prior id wt i/(2*S)
  have xp : 0≤x := by dsimp [x];positivity
  have xlt : x<Y := (div_lt_iff₀ (by positivity)).2 (mul_lt_mul_of_pos_left (by linarith : prior id wt i<2*S) hy)
  have strict : ⌊x⌋₊<Y := (Nat.floor_lt xp).mpr xlt
  have hrow : (row (Y:=Y) id wt S i).val=⌊x⌋₊ := by
    change min ⌊x⌋₊ (Y-1)=⌊x⌋₊
    exact min_eq_left (by omega)
  rw [hrow]
  exact ⟨(le_div_iff₀ (by positivity : 0<2*S)).mp (Nat.floor_le xp),
    (div_lt_iff₀ (by positivity : 0<2*S)).mp (Nat.lt_floor_add_one x)⟩

/-- Bounding the true number of whole input bits in a row only needs the
first and last positive occupant, even if zero items occur in between. -/
theorem bound (S B : ℝ) (hS : 0≤S) (pos : ∀i,0≤wt i) (small : ∀i,wt i≤B)
    (full : ∑i,wt i≤2*S) (scale : (Y:ℝ)*B≤S) (r : Fin Y) :
    inputLoad Finset.univ wt (row id wt S) r≤3*S/Y := by
  let occupied := Finset.univ.filter fun i=>row id wt S i=r ∧ 0<wt i
  have sum_eq : inputLoad Finset.univ wt (row id wt S) r=∑i∈occupied,wt i := by
    unfold inputLoad
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases live : 0<wt i
    · simp [live]
    · have zero : wt i=0 := by linarith [pos i]
      simp [zero]
  rw [sum_eq]
  have hy : (0:ℝ)<Y := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Y)
  by_cases populated : occupied.Nonempty
  · obtain ⟨a,ha,first⟩ := Finset.exists_min_image occupied id populated
    obtain ⟨b,hb,last⟩ := Finset.exists_max_image occupied id populated
    have aval := (Finset.mem_filter.mp ha).2
    have bval := (Finset.mem_filter.mp hb).2
    have pr : 0≤prior id wt a := Finset.sum_nonneg fun i _=>pos i
    have env := (endpoint id wt pos a).trans full
    have positive : 0<S := by linarith [aval.2]
    have lo := (bracket id wt positive pos full aval.2 (Y:=Y)).1
    have hi := (bracket id wt positive pos full bval.2 (Y:=Y)).2
    rw [aval.1] at lo
    rw [bval.1] at hi
    let A := DescentOrderedWords.before id a
    let Z := insert b (DescentOrderedWords.before id b)
    have dis : Disjoint A occupied := by
      apply Finset.disjoint_left.mpr
      intro i before paid
      exact (not_lt_of_ge (first i paid)) (Finset.mem_filter.mp before).2
    have cover : A∪occupied⊆Z := by
      intro i mem
      rcases Finset.mem_union.mp mem with pre|paid
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_lt_of_le
          (Finset.mem_filter.mp pre).2 (last a ha)⟩)
      · rcases (last i paid).lt_or_eq with lt|eq
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt⟩)
        · exact Finset.mem_insert.mpr (Or.inl (id.injective eq))
    have span := Finset.sum_le_sum_of_subset_of_nonneg (f:=wt) cover (fun i _ _=>pos i)
    rw [Finset.sum_union dis] at span
    have absent : b∉DescentOrderedWords.before id b := by simp [DescentOrderedWords.before]
    dsimp only [Z,A] at span
    rw [Finset.sum_insert absent] at span
    change prior id wt a+(∑i∈occupied,wt i)≤wt b+prior id wt b at span
    apply (le_div_iff₀ hy).2
    nlinarith only [mul_le_mul_of_nonneg_left span hy.le,lo,hi,mul_le_mul_of_nonneg_left (small b) hy.le,scale]
  · rw [Finset.not_nonempty_iff_eq_empty.mp populated,Finset.sum_empty]
    positivity

/-- On the actual integral accounting grid the real-valued specification
compiles to a single natural multiplication and a division. -/
theorem integer_read (size : I→ℕ) (S : ℕ) (i : I) :
    (row (Y:=Y) id (fun a=>(size a:ℝ)) S i).val=
      min (Y*DescentOrderedWords.offset id size i/(2*S)) (Y-1) := by
  have sum : prior id (fun a=>(size a:ℝ)) i=(DescentOrderedWords.offset id size i : ℕ) := by
    simp [prior,DescentOrderedWords.offset,Nat.cast_sum]
  change min ⌊(Y:ℝ)*prior id (fun a=>(size a:ℝ)) i/(2*(S:ℝ))⌋₊ _=_
  have denom : (2:ℝ)*S = ((2*S:ℕ):ℝ) := by push_cast; rfl
  rw [sum,←Nat.cast_mul,denom]
  rw [Nat.floor_div_eq_div]

end
end Hierarchy.DescentBaseProfile.Cumulative

end OAI
