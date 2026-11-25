import OAI.Hierarchy.DescentPackingColors
import OAI.Hierarchy.DescentColonyLayout
import OAI.Hierarchy.DescentFirstMinimumRAM

namespace OAI
/-! # The first minimizing affine sign computed from the integer colony loads -/

namespace Hierarchy.DescentAffineColors

open DescentWalshTables DescentColonies Finset
open scoped BigOperators Classical
noncomputable section

abbrev Candidate (k : ℕ) := Fin (2^(k+1))

/-- The last bit chooses the affine offset. Candidate order is the unsigned block order. -/
def code {k : ℕ} (a : Bits k) (b : ZMod 2) : Candidate k :=
  address (k+1) (Fin.snoc a b)
def linear {k : ℕ} (j : Candidate k) : Bits k := Fin.init ((address (k+1)).symm j)
def offset {k : ℕ} (j : Candidate k) : ZMod 2 := (address (k+1)).symm j (Fin.last k)
def thick {k : ℕ} (j : Candidate k) (i : Block k) : Bool :=
  decide (binaryRow (linear j) ((address k).symm i) + offset j = 0)

@[simp] theorem linear_code {k : ℕ} (a : Bits k) (b : ZMod 2) :
    linear (code a b) = a := by simp [linear,code]
@[simp] theorem offset_code {k : ℕ} (a : Bits k) (b : ZMod 2) :
    offset (code a b) = b := by simp [offset,code]

def side {k : ℕ} (A : Block k → ℕ) (j : Candidate k) (s : Bool) : ℕ :=
  ∑ i, if thick j i = s then A i else 0
def difference (a b : ℕ) : ℕ := if a≤b then b-a else a-b
def score {k C : ℕ} (A : Fin C → Block k → ℕ) (j : Candidate k) : ℕ :=
  ∑ c, difference (side (A c) j true) (side (A c) j false)

theorem side_le {k : ℕ} (A : Block k → ℕ) (j : Candidate k) (s : Bool) :
    side A j s ≤ ∑ i,A i :=
  sum_le_sum fun i _=>by split <;> simp

theorem score_le {k C : ℕ} (A : Fin C → Block k → ℕ) (j : Candidate k) :
    score A j ≤ ∑ c,∑ i,A c i := by
  apply sum_le_sum
  intro c _
  have yes := side_le (A c) j true
  have no := side_le (A c) j false
  unfold difference
  split <;> omega

private theorem unsigned_cast (a b : ℕ) :
    (difference a b:ℝ) = |(a:ℝ)-b| := by
  by_cases h : a≤b
  · rw [difference,ite_eq_left h,Nat.cast_sub h,abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · rw [difference,ite_eq_right h,Nat.cast_sub (by omega),abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (show b≤a by omega)))]

def imbalance {k : ℕ} (A : Block k→ℕ) (a : Bits k) (b : ZMod 2) : ℝ :=
  |∑ i, sign (binaryRow a i + b) * (A (address k i):ℝ)|

theorem read_score {k C : ℕ} (A : Fin C → Block k → ℕ) (j : Candidate k) :
    (score A j:ℝ) = ∑ c, imbalance (A c) (linear j) (offset j) := by
  rw [score,Nat.cast_sum]
  apply sum_congr rfl
  intro c _
  rw [unsigned_cast,imbalance]
  apply congrArg abs
  simp only [side,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,←sum_sub_distrib]
  rw [← (address k).sum_comp]
  apply sum_congr rfl
  intro i _
  by_cases yes : binaryRow (linear j) i + offset j=0 <;> simp [thick,sign,yes]

/-- This natural objective is defined even at malformed score-bank keys. -/
def scoreAt {k C : ℕ} (A : Fin C → Block k → ℕ) (i : ℕ) : ℕ :=
  if h:i<2^(k+1) then score A ⟨i,h⟩ else 0

/-- Same candidates and tie order as the physical first-minimum scan. -/
theorem first {k C : ℕ} (A : Fin C → Block k → ℕ) :
    ∃ j : Candidate k,
      (scanMinimum (scoreAt A) (List.range (2^(k+1)))).1=some (j.val,score A j) ∧
      ∀ u,score A j ≤ score A u := by
  have spec := (scanMinimum_spec (scoreAt A) (List.range (2^(k+1)))).2
  cases e : (scanMinimum (scoreAt A) (List.range (2^(k+1)))).1 with
  | none =>
    rw [e] at spec
    have len := congrArg List.length spec
    simp at len
  | some p =>
    rw [e] at spec
    have actual : p.1∈List.range (2^(k+1)) :=
      DescentFirstMinimumRAM.winner_mem (scoreAt A) _ (s:=p.1) (a:=p.2) e
    have valid := List.mem_range.mp actual
    let j : Candidate k := ⟨p.1,valid⟩
    have val : p.2=score A j := spec.1.trans (dite_eq_left valid)
    refine ⟨j,?_,fun u=>?_⟩
    · exact congrArg some (Prod.ext rfl val)
    · have le := spec.2 u.val (List.mem_range.mpr u.isLt)
      simpa only [scoreAt,dite_eq_left u.isLt,val] using le

/-- Unused public colony slots do not increase the square-root term. Only
the real active colony count occurs in the bound. -/
theorem winner_bound {k C : ℕ} (A : Fin C→Block k→ℕ) (live : Finset (Fin C)) (B : ℕ)
    (off : ∀c∉live, ∀i,A c i=0) (small : ∀c i,A c i≤B) (j : Candidate k)
    (best : ∀u,score A j ≤ score A u) :
    (score A j:ℝ) ≤ Real.sqrt ((B:ℝ)*live.card*∑c,∑i,(A c i:ℝ)) := by
  obtain ⟨a,b,paint⟩ := DescentPackingColors.exists_coloring
    (fun (c : live) i=>(A c.val (address k i):ℝ)) (B:ℝ) (fun _ _=>by positivity)
    (fun c i=>by exact_mod_cast small c.val (address k i))
  have extend (f : Fin C→ℝ) (zero : ∀c∉live,f c=0) : ∑c:live,f c.val=∑c,f c :=
    (Finset.sum_subtype live (fun _=>Iff.rfl) f).symm.trans
      (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi=>zero i hi))
  have lhs := extend (fun c=>imbalance (A c) a b) (fun c hc=>by simp [imbalance,off c hc])
  have rhs := extend (fun c=>∑ i : Block k,(A c i:ℝ)) (fun c hc=>by simp [off c hc])
  have re := fun c : Fin C => (address k).sum_comp (fun i=>(A c i:ℝ))
  change ∑c:live,imbalance (A c.val) a b ≤ _ at paint
  simp only [lhs,re,rhs,Fintype.card_coe] at paint
  have minimum : (score A j:ℝ) ≤ score A (code a b) := by exact_mod_cast best (code a b)
  rw [read_score A (code a b),linear_code,offset_code] at minimum
  exact minimum.trans paint

/-- The score of each complete candidate is unchanged when unused directory
slots are erased and occupied rows are enumerated in any fixed order. -/
theorem score_on_directory {k C : ℕ} {U : Type*} [Fintype U]
    (A : Fin C→Block k→ℕ) (slot : U ↪ Fin C) (load : U→Bits k→ℕ)
    (rows : ∀ c i, A (slot c) (address k i)=load c i)
    (unused : ∀ c, c∉Set.range slot → ∀ i,A c i=0) (j : Candidate k) :
    score A j = score (fun (t : Fin (Fintype.card U)) x=>
      load ((Fintype.equivFin U).symm t) ((address k).symm x)) j := by
  let f := fun c=>difference (side (A c) j true) (side (A c) j false)
  have zero (c : Fin C) (_ : c∈(Finset.univ : Finset (Fin C))) (miss : c∉Finset.univ.map slot) : f c=0 := by
    have off : c∉Set.range slot := fun ⟨u,eqn⟩=>miss (Finset.mem_map.mpr ⟨u,Finset.mem_univ _,eqn⟩)
    simp [f,side,difference,unused c off]
  change (∑ c,f c)=_
  rw [←Finset.sum_subset (Finset.subset_univ (Finset.univ.map slot)) zero,Finset.sum_map]
  unfold score
  rw [←(Fintype.equivFin U).sum_comp]
  apply Finset.sum_congr rfl
  intro u _
  have equal : A (slot u) = (fun x=>load u ((address k).symm x)) := by
    funext x
    simpa using rows u ((address k).symm x)
  simp only [Equiv.symm_apply_apply,f,equal]

/-- Read the winning unsigned score on the actual occupied colonies, using
their distinct directory slots. All other rows have zero mass. -/
theorem occupied_bound {k C : ℕ} {U : Type*} [Fintype U]
    (A : Fin C→Block k→ℕ) (slot : U ↪ Fin C) (load : U→Bits k→ℕ)
    (rows : ∀ c i, A (slot c) (address k i)=load c i)
    (unused : ∀ c, c∉Set.range slot → ∀ i,A c i=0)
    (B : ℕ) (small : ∀c i,load c i≤B) (j : Candidate k) (best : ∀u,score A j ≤ score A u) :
    ∑ c, |∑ i, sign (binaryRow (linear j) i+offset j)*(load c i:ℝ)| ≤
      Real.sqrt ((B:ℝ)*Fintype.card U*∑c,∑i,(load c i:ℝ)) := by
  have scored (u : Candidate k) : (score A u:ℝ) =
      ∑ c, |∑ i,sign (binaryRow (linear u) i+offset u)*(load c i:ℝ)| := by
    rw [read_score]
    let f := fun c=>imbalance (A c) (linear u) (offset u)
    have zero (v) (_ : v∈(Finset.univ : Finset (Fin C))) (miss : v∉Finset.univ.map slot) : f v=0 := by
      have off : v∉Set.range slot := fun ⟨src,eqn⟩ => miss (Finset.mem_map.mpr ⟨src,Finset.mem_univ _,eqn⟩)
      simp [f,imbalance,unused v off]
    change (∑c,f c)=_
    rw [←Finset.sum_subset (Finset.subset_univ (Finset.univ.map slot)) zero,Finset.sum_map]
    simp only [f,imbalance,rows]
  obtain ⟨a,b,bound⟩ := DescentPackingColors.exists_coloring (fun c i=>(load c i:ℝ))
    (B:ℝ) (fun _ _=>by positivity) (fun c i=>by exact_mod_cast small c i)
  have compare : (score A j:ℝ) ≤ score A (code a b) := by exact_mod_cast best (code a b)
  rw [scored j,scored (code a b),linear_code,offset_code] at compare
  exact compare.trans bound

end
end Hierarchy.DescentAffineColors

end OAI
