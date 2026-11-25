import OAI.Hierarchy.DescentGLNielsenOps

namespace OAI
/-! # Isolating one coordinate of an arbitrary measured binary linear layout -/

noncomputable section
namespace Hierarchy.DescentGLNielsen
open DescentGL
open scoped BigOperators Classical
variable {m : ℕ}

def axis (j : Fin m) : Bits m := Pi.single j 1

@[simp] theorem axis_self (j : Fin m) : axis j j=1 := by simp [axis]
@[simp] theorem axis_other {i j : Fin m} (ne : i≠j) : axis j i=0 := by simp [axis,Pi.single_eq_of_ne ne]

private theorem axis_ne_zero (i : Fin m) : axis i≠0 := by
  intro h
  have := congrFun h i
  simp at this

private theorem initial_nonzero (L : Layout (m+1)) : L (axis 0)≠0 :=
  fun h=>axis_ne_zero _ (L.injective (h.trans L.map_zero.symm))

private theorem one_of_ne (x : ZMod 2) (h : x≠0) : x=1 :=
  (show ∀a : ZMod 2,a≠0→a=1 by decide) x h

private theorem has_pivot (L : Layout (m+1)) (empty : L (axis 0) 0=0) :
    ∃j : Fin m,L (axis 0) j.succ=1 := by
  by_contra! negative
  apply initial_nonzero L
  funext i
  exact Fin.cases empty (fun j=>by
    by_contra ne
    exact negative j (one_of_ne _ ne)) i

def pivot (L : Layout (m+1)) : Bits m :=
  if h : L (axis 0) 0=0 then axis (has_pivot L h).choose else 0

def prepared (L : Layout (m+1)) : Layout (m+1) := L.trans (layout (headPlan (pivot L)))
def other (L : Layout (m+1)) : Bits m := Fin.tail (prepared L (axis 0))
def clean (L : Layout (m+1)) := (prepared L).trans (layout (tailPlan (other L)))

theorem prepared_head (L : Layout (m+1)) : prepared L (axis 0) 0=1 := by
  change layout (headPlan (pivot L)) (L (axis 0)) 0=1
  rw [layout_apply,head_plan,Fin.cons_zero]
  by_cases h : L (axis 0) 0=0
  · let i := (has_pivot L h).choose
    have hit : L (axis 0) i.succ=1 := (has_pivot L h).choose_spec
    simp only [pivot,h,zero_add]
    change (∑j : Fin m,axis i j * L (axis 0) j.succ)=1
    rw [Finset.sum_eq_single i]
    · simp [hit]
    · intro j _ ne;simp [axis_other ne]
    · simp
  · simp [pivot,one_of_ne _ h]

theorem clean_axis (L : Layout (m+1)) : clean L (axis 0)=axis 0 := by
  change layout (tailPlan (other L)) (prepared L (axis 0))=axis 0
  rw [layout_apply,tail_plan]
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [prepared_head]
  · simp [other,Fin.tail,prepared_head,CharTwo.add_self_eq_zero]

private theorem coordinates (L : Layout m) (x : Bits m) (i : Fin m) :
    L x i=∑j,x j*L (axis j) i := by
  let B := Pi.basisFun (ZMod 2) (Fin m)
  have s := congrArg (fun y : Bits m=>L y i) (B.sum_repr x)
  symm
  simpa [B,Pi.basisFun_repr,Pi.basisFun_apply,axis,map_sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using s

def leading (L : Layout (m+1)) (j : Fin m) : ZMod 2 := clean L (axis j.succ) 0

def reduced (L : Layout (m+1)) : Layout (m+1) :=
  (layout (headPlan (leading L))).trans (clean L)

theorem reduced_head (L : Layout (m+1)) (x : Bits (m+1)) : reduced L x 0=x 0 := by
  change clean L (layout (headPlan (leading L)) x) 0=x 0
  rw [layout_apply,head_plan,coordinates (clean L),Fin.sum_univ_succ,clean_axis]
  simp only [axis_self,Fin.cons_zero,Fin.cons_succ,Fin.tail,mul_one]
  change (x 0+∑j,leading L j*x j.succ)+(∑j,x j.succ*leading L j)=_
  have comm : (∑j,x j.succ*leading L j)=∑j,leading L j*x j.succ :=
    Finset.sum_congr rfl (fun _ _=>mul_comm ..)
  rw [comm,add_assoc,CharTwo.add_self_eq_zero,add_zero]

theorem reduced_axis (L : Layout (m+1)) : reduced L (axis 0)=axis 0 := by
  have same : applyList (headPlan (leading L)) (axis 0)=axis (0:Fin (m+1)) := by
    rw [head_plan]
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · simp [axis]
    · rfl
  change clean L (layout (headPlan (leading L)) (axis 0))=_
  rw [layout_apply,same,clean_axis]

def embed : Bits m→ₗ[ZMod 2] Bits (m+1) where
  toFun := Fin.cons (α := fun _ : Fin (m+1) => ZMod 2) 0
  map_add' x y := by funext i;exact Fin.cases (by simp) (fun _=>rfl) i
  map_smul' a x := by funext i;exact Fin.cases (by simp) (fun _=>rfl) i

def drop : Bits (m+1)→ₗ[ZMod 2] Bits m where
  toFun := Fin.tail
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lower (L : Layout (m+1)) : Layout m :=
  let g := drop.comp ((reduced L).toLinearMap.comp embed)
  LinearEquiv.ofBijective g <| (Fintype.bijective_iff_injective_and_card _).2 ⟨by
    intro x y h
    have top : reduced L (embed x)=reduced L (embed y) := by
      funext i
      exact Fin.cases (by simp only [reduced_head]; rfl) (fun j=>congrFun h j) i
    have eqn := (reduced L).injective top
    exact funext (fun j=>congrFun eqn j.succ),rfl⟩

theorem reduced_apply (L : Layout (m+1)) (x : Bits (m+1)) :
    reduced L x=Fin.cons (x 0) (lower L (Fin.tail x)) := by
  have parts : x=embed (Fin.tail x)+x 0 • axis (0:Fin (m+1)) := by
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · simp [embed,smul_eq_mul]
    · simp [embed,smul_eq_mul,Fin.tail]
  funext i
  refine Fin.cases (by simp [reduced_head]) (fun j=>?_) i
  conv_lhs => rw [parts,map_add,map_smul,reduced_axis]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,axis_other j.succ_ne_zero,mul_zero,add_zero,Fin.cons_succ]
  rfl

end Hierarchy.DescentGLNielsen

end
end OAI
