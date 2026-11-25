import OAI.Optimization.LinearProgramming.Elimination.MaskSolve

/-! Augmenting the ordered row list by the right-hand side both detects inconsistency
and makes its Gram right-hand side available as a contiguous row in memory. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination
open Matrix Module Submodule
open scoped Matrix BigOperators
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m d : ℕ}

/-- The right-hand side, then the input columns. The descending basis scan tests `b` last. -/
def augmentedRows (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) : Matrix (Fin (d+1)) (Fin m) K :=
  Fin.cons b A.col

private def shifted (s : Finset (Fin d)) : Finset (Fin (d+1)) := s.map (Fin.succEmb d)

@[simp] private theorem zero_not_shifted (s : Finset (Fin d)) : (0 : Fin (d+1)) ∉ shifted s := by
  simp [shifted,Finset.mem_map]

@[simp] private theorem succ_mem_shifted (s : Finset (Fin d)) (j : Fin d) : j.succ ∈ shifted s ↔ j∈s := by
  simp [shifted,Finset.mem_map]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem shifted_indep (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) (s : Finset (Fin d)) :
    LinearIndepOn K (augmentedRows A b).row (shifted s : Set (Fin (d+1))) ↔ LinearIndepOn K A.col (s : Set (Fin d)) := by
  let e := Finset.equivMap (Fin.succEmb d) s
  exact (linearIndependent_equiv' e rfl).symm

private theorem scan_shifted (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) (js : List (Fin d)) :
    let T := augmentedRows A b
    scanMask (T*Tᵀ) (js.map Fin.succ) = shifted (scanMask (Aᵀ*A) js) := by
  let T:=augmentedRows A b
  change scanMask (T*Tᵀ) (js.map Fin.succ) = _
  induction js with
  | nil => simp [scanMask,shifted]
  | cons j js ih =>
    let s := scanMask (Aᵀ*A) js
    have eqs : insert j.succ (shifted s) = shifted (insert j s) := by simp [shifted]
    have hi : determinant (maskGram (T*Tᵀ) (flag (insert j.succ (shifted s)))) ≠ 0 ↔
        determinant (maskGram (Aᵀ*A) (flag (insert j s))) ≠ 0 := by
      rw [eqs,maskGram_det_ne_zero_iff A]
      have h := maskGram_det_ne_zero_iff Tᵀ (shifted (insert j s))
      rw [Matrix.transpose_transpose] at h
      exact h.trans (shifted_indep A b _)
    simp only [List.map_cons,scanMask,ih]
    change (if determinant (maskGram (T*Tᵀ) (flag (insert j.succ (shifted s))))=0 then shifted s else insert j.succ (shifted s)) =
      shifted (if determinant (maskGram (Aᵀ*A) (flag (insert j s)))=0 then s else insert j s)
    by_cases h : determinant (maskGram (Aᵀ*A) (flag (insert j s)))=0
    · have z : determinant (maskGram (T*Tᵀ) (flag (insert j.succ (shifted s))))=0 := by
        by_contra hn;exact hi.mp hn h
      rw [ite_eq_left z,ite_eq_left h]
    · rw [ite_eq_right (hi.mpr h),ite_eq_right h,eqs]

/-- The extra first flag tests consistency. Every ordinary column flag agrees exactly with
the variable-width deterministic solver, even when the solution is nonunique. -/
theorem augmented_basis (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) :
    let T := augmentedRows A b
    let S := basisMask (T*Tᵀ)
    (0 ∉ S ↔ ∃ x,A *ᵥ x=b) ∧ ∀j : Fin d, j.succ ∈ S ↔ j∈basisMask (Aᵀ*A) := by
  classical
  let s := basisMask (Aᵀ*A)
  let T := augmentedRows A b
  let G := T*Tᵀ
  let V := shifted s
  have prev : scanMask G ((List.finRange d).map Fin.succ)=V := scan_shifted A b _
  have vs : LinearIndepOn K T.row (V : Set (Fin (d+1))) := (shifted_indep A b _).2 (scanMask_spec A _).1
  have image : T.row '' (V : Set (Fin (d+1)))=A.col '' (s : Set (Fin d)) := by
    change T.row '' ((s.map (Fin.succEmb d)) : Set (Fin (d+1))) = _
    rw [Finset.coe_map,Set.image_image];rfl
  have fresh : (0 : Fin (d+1)) ∉ (V : Set (Fin (d+1))) := zero_not_shifted s
  have criterion : determinant (maskGram G (flag (insert 0 V)))≠0 ↔ ¬∃x,A*ᵥ x=b := by
    have hh := maskGram_det_ne_zero_iff Tᵀ (insert 0 V)
    rw [Matrix.transpose_transpose] at hh
    apply hh.trans
    change LinearIndepOn K T.row ((insert 0 V : Finset (Fin (d+1))) : Set (Fin (d+1))) ↔ _
    rw [Finset.coe_insert,linearIndepOn_insert fresh,and_iff_right vs,image,
      show span K (A.col '' (s : Set (Fin d))) =_ from basisMask_span A,← Matrix.range_mulVecLin]
    rfl
  have ends : basisMask G = if (∃x,A*ᵥ x=b) then V else insert 0 V := by
    simp only [basisMask,List.finRange_succ,scanMask,prev]
    by_cases h:∃x,A*ᵥ x=b
    · have hd : determinant (maskGram G (flag (insert 0 V)))=0 := by by_contra hv;exact criterion.mp hv h
      rw [ite_eq_left hd,ite_eq_left h]
    · rw [ite_eq_right (criterion.mpr h),ite_eq_right h]
  change (0 ∉ basisMask G ↔ _) ∧ ∀j : Fin d,j.succ∈basisMask G ↔ j∈s
  rw [ends]
  by_cases h : ∃x,A*ᵥ x=b <;> simp [h,V]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Clear inactive coordinates after solving against an unmasked right-hand side. With an
invertible masked Gram matrix this exactly recovers the original supported coefficients. -/
theorem masked_inverse_coordinates {r : ℕ} (G : Matrix (Fin r) (Fin r) K) (s : Finset (Fin r))
    (x rhs : Fin r→K) (hG : G*ᵥx=rhs) (hz : ∀i∉s,x i=0)
    (hd : (maskGram G (flag s)).det≠0) :
    (fun i => flag s i * ((maskGram G (flag s))⁻¹ *ᵥ rhs) i) = x := by
  let w (i : Fin r) := if i∈s then x i else rhs i
  have hw0 : (fun i=> (flag s i : K)*w i)=x := by
    funext i;by_cases h:i∈s <;> simp [flag,w,h,hz i]
  have hw : maskGram G (flag s) *ᵥ w=rhs := by
    funext i;rw [maskGram_mulVec,hw0,hG]
    by_cases h:i∈s <;> simp [flag,w,h]
  have hrep : (maskGram G (flag s))⁻¹ *ᵥ rhs = w := by
    rw [←hw,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),Matrix.one_mulVec]
  simpa only [hrep] using hw0

/-- The static augmented Gram, its flag table, and one masked inverse recover a canonical
solution. The statement uses the exact coordinate formula emitted by the RAM routines. -/
theorem augmented_recovery (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) (x : Fin d→K)
    (hx : A*ᵥx=b) (hz : ∀i∉basisMask (Aᵀ*A), x i=0) :
    let T := augmentedRows A b
    let G := T*Tᵀ
    let s := basisMask G
    let u := (maskGram G (flag s))⁻¹ *ᵥ G 0
    ∀j : Fin d,flag s j.succ*u j.succ=x j := by
  let T := augmentedRows A b
  let G := T*Tᵀ
  let s := basisMask G
  let x' : Fin (d+1)→K := Fin.cons 0 x
  have hsol : Tᵀ *ᵥ x'=b := by
    ext i;change (∑j : Fin (d+1), T j i * x' j)=b i
    rw [Fin.sum_univ_succ]
    simp only [x',T,augmentedRows,Fin.cons_zero,Fin.cons_succ,mul_zero,zero_add]
    simpa only [Matrix.mulVec,dotProduct,Matrix.col,Matrix.transpose_apply] using congrFun hx i
  have hG : G *ᵥ x'=G 0 := by
    change (T*Tᵀ) *ᵥ x' = _
    rw [←Matrix.mulVec_mulVec,hsol];funext i
    change (∑k : Fin m,T i k*b k)=∑k : Fin m,T 0 k*T i k
    exact Finset.sum_congr rfl fun k _=>mul_comm ..
  have hz' : ∀i∉s,x' i=0 := by
    intro i;refine Fin.cases (fun _=>rfl) (fun j h=>?_) i
    exact hz j (fun hj=>h ((augmented_basis A b).2 j |>.2 hj))
  have hli : LinearIndepOn K T.row (s : Set (Fin (d+1))) := by
    change LinearIndepOn K Tᵀ.col (scanMask (T*Tᵀ) (List.finRange (d+1)) : Set (Fin (d+1)))
    simpa only [Matrix.transpose_transpose] using (scanMask_spec Tᵀ (List.finRange (d+1))).1
  have hd : (maskGram G (flag s)).det≠0 := by
    have hh := maskGram_det_ne_zero_iff Tᵀ s
    rw [Matrix.transpose_transpose,determinant_eq] at hh
    exact hh.mpr hli
  exact fun j=>congrFun (masked_inverse_coordinates G s x' (G 0) hG hz' hd) j.succ

end Elimination
end LinearProgramming
end Optimization
end OAI
