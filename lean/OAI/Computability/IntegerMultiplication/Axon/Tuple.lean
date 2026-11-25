import OAI.Computability.IntegerMultiplication.Axon.Factor

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Axon
open Net Net.Tensor Net.Walsh Strip Code IntegerMultiplication.Fourier
open Matrix Finset
variable {k : ℕ} {I : Type} [Fintype I] [DecidableEq I]
noncomputable section
abbrev Scr (I : Type) (k : ℕ) := I→Face k
abbrev Drop (j : Fin k) := {q:Fin k // q≠j}
def clip (i:Fin k) : Face k ≃ B × (Drop i → B) where
  toFun x := (x i,fun j=> x j.val)
  invFun x := fun j=> if h:j=i then x.1 else x.2 ⟨j,h⟩
  left_inv x := by funext j; dsimp; split <;> simp_all
  right_inv x := by
    refine Prod.ext (by simp) (funext fun j=> ?_)
    exact dite_eq_right j.2
abbrev mains (i:Fin k) : Lens (Scr I k) (Walsh.Addr I) (I → Drop i → B) where
  toFun x := (fun j=> (clip i (x j)).1,fun j=> (clip i (x j)).2)
  invFun x := fun j=> (clip i).symm (x.1 j,x.2 j)
  left_inv x := funext fun j=> by simpa only [Prod.mk.eta] using (clip i).symm_apply_apply (x j)
  right_inv x := by
    simp only [Equiv.apply_symm_apply]
variable {R:Type} [CommRing R] (i:Fin k) (M : Tensor.Mat B R)
omit [Fintype I] [DecidableEq I] in
theorem off (x y : Scr I k) :
    (mains i x).2=(mains i y).2 ↔ ∀ v,E i (x v) (y v)=true := by
  simp only [E,decide_eq_true_eq]
  constructor
  · intro t v j h
    exact congrFun (congrFun t v) ⟨j,h⟩
  intro q; exact funext fun v=> funext fun j=> q _ j.val j.2

def zoom : Mat (Scr I k) R :=
  mat (fun (_:I)=> Matrix.of (fun x y=> if E i x y then M (x i) (y i) else 0))

omit [DecidableEq I] in
theorem zoomed (x y : Scr I k) :
    zoom i M x y= if (mains i x).2=(mains i y).2 then
      mat (fun (_:I)=>M) (mains i x).1 (mains i y).1 else 0 := by
  classical
  rw [zoom]
  simp only [app,of_apply]
  split
  next h =>
    apply prod_congr rfl; intro j _
    rw [ite_eq_left ((off i x y).1 h _)]; rfl
  next h =>
    obtain ⟨j,e⟩ := not_forall.mp (not_iff_not.mpr (off i x y) |>.mp h)
    apply prod_eq_zero (mem_univ j) (ite_eq_right e)
theorem regard (x : Scr I k→R) :
    zoom i M *ᵥ x = Strip.Optic.operate (mains i) (mat (fun (_:I)=>M)) x := by
  unfold Strip.Optic.operate
  rw [← Phase.align] -- grid def
  congr 1
  ext a b
  exact zoomed ..  -- rfl grid?
def who (i:Fin k) (x : Scr I k) (v : I) := x v i
abbrev replaceAt (i:Fin k) (x:Scr I k) (z : I→ B) : Scr I k :=
  fun v=> Function.update (x v) i (z v)

theorem retinal (x : Scr I k→R) (a:Scr I k) :
    (zoom i M *ᵥ x) a =
      ∑ z : Addr I, mat (fun (_:I)=>M) (who i a) z * x (replaceAt i a z) := by
  rw [regard]
  change (∑ y,mat (fun (_:I)=>M) (who i a) y*x ((mains i).symm (y,(mains i a).2)))=_
  apply sum_congr rfl
  intro p _
  suffices h : (mains i).symm (p,(mains i a).2)=replaceAt i a p by rw [h]
  funext j b
  change (if h:b=i then p j else a j (⟨b,h⟩:Drop i).val)=Function.update (a j) i _ b
  split
  next t => subst b; simp
  next t => rw [Function.update_of_ne t]

-- target assembly
variable (q:I→ℤ)
def spotM :=
  mat (fun j:I => layer (q j) i)
def twine (x:Scr I k) :=
  ∏ j, frequency (q j) i (x j)
omit [DecidableEq I] in
theorem twine_ok (x : Scr I k) :
    ‖twine i q x‖=1 := by
  unfold twine
  simp [norm_prod,frequency,R] -- mathlib normProd?
theorem spot_eq :
    spotM i q = diagonal (twine i q) * zoom i F := by
  unfold spotM layer
  rw [← Tensor.multiply,zoom,headH]
  congr 1
  exact Tensor.diag _

-- exponent as shared r
abbrev gloss (x : Scr I k) : ℤ :=
  2^i.val*∑ j:I,q j*(pin (x j i) : ℤ)*beyond (x j) i

theorem wave (x : Scr I k) :
    twine i q x=IntegerMultiplication.Axon.R k (gloss i q x) := by
  unfold twine gloss
  have e (s : Finset I) :
      ∏ j∈s,frequency (q j) i (x j)=
      IntegerMultiplication.Axon.R (k-i.val) (∑ j∈s,q j*(pin (x j i):ℤ)*beyond (x j) i) := by
    induction s using Finset.induction_on with
    | empty=> simp [Axon.R,phase]
    | insert j s h ih=> rw [prod_insert h,sum_insert h,ih]; simp only [Axon.R,frequency,phase_add]
  rw [e]
  generalize (∑ j:I, q j*(pin (x j i):ℤ)*beyond (x j) i)=a
  have h : i.val+(k-i.val)=k := by have := i.isLt; omega
  have b : (2^k : ℕ)=2^i.val*2^(k-i.val) := by rw [← pow_add,h]
  rw [Axon.R,Axon.R,phase,phase,b]
  congr 1
  push_cast
  field_simp

-- apply in order
def flick : (Scr I k→ℂ) × Fin k → Scr I k→ℂ :=
  fun v => spotM v.2 q *ᵥ v.1
theorem orderR (l : List (Fin k)) (x : Scr I k→ℂ) :
    l.foldl (fun x i=> flick q (x,i)) x = mat (fun j:I=> play (q j) l) *ᵥ x := by
  induction l generalizing x with
  | nil=>
    change x=mat (fun _=> (1:Mb k)) *ᵥ x
    rw [Tensor.unit,one_mulVec]
  | cons i l ih=>
    rw [List.foldl_cons,ih]
    change mat _ *ᵥ (mat (fun j:I=> layer (q j) i)*ᵥ x)=mat (fun j:I=>play (q j) l*layer (q j) i)*ᵥ x
    rw [mulVec_mulVec,Tensor.multiply]

abbrev pix (x:Scr I k) : I→Spot (2^k) := localE k ∘ x
def pixel : Scr I k ≃ (I→Spot (2^k)) where
  toFun := pix
  invFun x := (localE k).symm ∘ x
  left_inv _ := by simp [pix,Function.comp_def]
  right_inv _ := by simp [pix,Function.comp_def]
def mDFT (x:(I→Spot (2^k))→ℂ) : (I→Spot (2^k))→ℂ :=
  fun v=> (mat (fun j:I=> Matrix.of fun a b:Spot (2^k)=> IntegerMultiplication.Axon.R k (q j*rep a*rep b)) *ᵥ x) v
abbrev reface (x:Scr I k) := refl_ ∘ x
theorem use (h:∀ i,Odd (q i)) (x:(I→Spot (2^k))→ℂ) (a:Scr I k):
    ((layers k).foldl (fun x i=> flick q (x,i)) (x ∘ pix)) (reface a) =
      mDFT q x (pix a) := by
  rw [orderR]; simp_rw [persist _ (h _)]
  unfold mDFT
  let m := fun v:I→Spot (2^k)=> mat (fun j:I=> Matrix.of fun c b=> IntegerMultiplication.Axon.R k (q j*rep c*rep b)) (pix a) v * x v
  change ∑ v,mat _ _ v*_ = ∑ v,m v
  rw [← (pixel (I:=I) (k:=k)).sum_comp m]
  apply sum_congr rfl
  intro j _
  unfold m
  congr 1
  unfold mat
  change (∏ v:I,lineF k (q v) (refl_ (a v)) (j v)) = ∏ v:I,Axon.R k ((q v)*(bold (a v):ℤ)*(bold (j v):ℤ))
  apply prod_congr rfl; intro i _
  unfold lineF; simp only [Matrix.of_apply,shine]
end
end Axon

end IntegerMultiplication
end Computability
end OAI
