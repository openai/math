import OAI.Computability.IntegerMultiplication.Axon.Rad

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Axon
open Net Net.Walsh Net.Tensor IntegerMultiplication.Fourier
open Matrix Finset
variable {k:ℕ} (i:Fin k)
noncomputable section
-- equality at all positions except one
def E (x y : Face k) : Bool :=
  decide (∀ j,j≠i→ x j=y j)
theorem inE (x y : Face (k+1)) :
    E 0 x y=true ↔ stem x=stem y := by
  simp only [E,decide_eq_true_eq]
  constructor
  · intro h; exact funext fun i=> h _ (Fin.succ_ne_zero _)
  intro h j; refine Fin.cases ?_ ?_ j
  · simp
  exact fun i _=> congrFun h _
theorem inEs (x y : Face (k+1)) :
    E i.succ x y = (decide (crest x=crest y)&& E i (stem x) (stem y)) := by
  unfold E
  suffices e : ((∀ j,j≠i.succ→ x j=y j)) ↔ crest x=crest y ∧ ∀ j,j≠i→ stem x j=stem y j by
    by_cases h:crest x=crest y <;> simp [*] -- remove

  constructor
  · intro h
    exact ⟨h _ (Ne.symm i.succ_ne_zero),fun j v=> h _ (by intro e; apply v; exact Fin.succ_injective _ e)⟩
  intro h j; refine Fin.cases (fun _=> h.1) ?_ j
  exact fun i x=> h.2 _ (fun e=> x (congrArg Fin.succ e))

-- one radix-two step
def headH (i:Fin k) : Mb k := Matrix.of fun x y =>
  if E i x y then (Walsh.F (x i) (y i)) else 0
def layer (q : ℤ) (i : Fin k) : Mb k :=
  diagonal (frequency q i) * headH i
theorem active (q : ℤ) (x y : Face k) :
    layer q i x y = frequency q i x * (if E i x y then Walsh.F (x i) (y i) else 0) := by
  rw [layer, mul_apply,Finset.sum_eq_single x]
  · rw [diagonal_apply,ite_eq_left rfl]; rfl
  · intros; rw [diagonal_apply,ite_eq_right (by grind),zero_mul]
  simp

-- tensor recurrence head/tail
def tap (M : Mb k) : Mb (k+1) :=
  Matrix.of fun x y => if crest x=crest y then M (stem x) (stem y) else 0
private theorem sum1 (g : Face (k+1) → ℂ) :
    ∑ i,g i = ∑ b:B,∑ x:Face k,g (branch (b,x)) := by
  rw [← Loom.join.sum_comp g, Fintype.sum_prod_type]
private theorem stamps (x y : Face (k+1)) : x=y ↔ crest x=crest y ∧ stem x=stem y := by
  simp only [← Prod.ext_iff (x:=(crest x,stem x)) (y:=(crest y,stem y))] -- arg names?
  exact Loom.join.symm.injective.eq_iff.symm

theorem atTap (x y : Face (k+1)) (M : Mb k) :
    tap M x y=if crest x=crest y then M (stem x) (stem y) else 0 := rfl
theorem tree (M S : Mb k) :
    tap (M*S) = tap M * tap S := by
  ext x y
  rw [Matrix.mul_apply,sum1,atTap,mul_apply]
  simp_rw [atTap, crest_b,stem_b,ite_mul,zero_mul]
  rw [Finset.sum_eq_single (crest x)]
  · simp only [ite_true, mul_ite,mul_zero]
    split <;> simp
  · intro j _ e; simp [Ne.symm e]
  simp
theorem tree1 : tap (k:=k) 1=1 := by
  ext x y
  simp only [atTap,Matrix.one_apply,stamps x y]
  by_cases v : crest x=crest y <;> by_cases e : stem x=stem y <;> simp [v,e]
theorem pulseS (q : ℤ) : layer q i.succ=tap (layer q i) := by
  ext x y
  rw [active,step,atTap,active,inEs]
  by_cases v: crest x=crest y <;> simp [v]

theorem combine (q : ℤ) (h : Odd q) : lineF (k+1) q=tap (lineF k q)*layer q 0 := by
  ext x y
  let r := lineF k q
  rw [first x y q h, mul_apply, sum1]
  simp_rw [atTap,active,stem_b,crest_b,ite_mul,zero_mul]
  rw [Finset.sum_eq_single (crest x)]
  · simp only [ite_true,inE,stem_b]
    rw [Finset.sum_eq_single (stem y)]
    · rw [ite_eq_left rfl]
    · intro j _ t; simp [t]
    simp
  · intro j _ t; simp [Ne.symm t]
  simp

-- run all l stages in increasing order.
def layers (n:ℕ) := List.ofFn (id (α:=Fin n))
def play (q : ℤ) (l:List (Fin k)) : Mb k :=
  l.foldr (fun i s=>s*layer q i) 1
theorem unfoldP (q:ℤ) (l:List (Fin k)) :
    play q (l.map Fin.succ) = tap (play q l) := by
  induction l with
  | nil=>exact tree1.symm
  | cons i l ih =>
    change play q (l.map Fin.succ)*layer q i.succ=tap (play q l*layer q i)
    rw [ih,pulseS,tree]
theorem persist (q:ℤ) (h:Odd q) :
    play q (layers k) = lineF k q := by
  induction k with
  | zero =>
    simp [play,layers]
    ext x y
    rw [Subsingleton.elim y x]
    change (1 : Mb 0) x x = R 0 (q*0*0)
    simp [Fourier.phase,R]
  | succ k ih =>
    have e : layers (k+1) = (0::(layers k).map Fin.succ) := by rw [layers,layers,List.ofFn_succ,List.map_ofFn]; rfl
    rw [combine _ h,e]
    change play q ((layers k).map Fin.succ)*_=_
    rw [unfoldP,ih]

-- interface single transform
theorem yields (q:ℤ) (h:Odd q) (z:Face k) (x : Arr (2^k) ℂ) :
    (play q (layers k) *ᵥ (x ∘ localE k)) (refl_ z) =
      dft _ (-q) x (localE k z) := by
  rw [persist q h]
  unfold dft; simp only [neg_neg]
  let p i := phase (2^k) (q*rep (localE k z)*rep i)*x i
  change ∑ i, lineF k q (refl_ z) i*x _=∑ i,p i
  rw [← (localE k).sum_comp p]
  apply Finset.sum_congr rfl
  intro i _
  unfold lineF; simp only [Matrix.of_apply,shine]
  rfl
end
end Axon

end IntegerMultiplication
end Computability
end OAI
