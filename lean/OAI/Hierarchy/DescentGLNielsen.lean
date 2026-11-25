import OAI.Hierarchy.DescentGLNielsenReduction
import OAI.Hierarchy.DescentGLNativeSelection

namespace OAI
/-! # A single quadratic instruction schedule for every measured invertible binary basis -/

noncomputable section
namespace Hierarchy.DescentGLNielsen
open DescentGL
open scoped Classical BigOperators

def schedule : (m : ℕ)→List (Gate m)
  | 0=>[]
  | m+1=>
    let heads := (List.finRange m).map intoHead
    let tails := (List.finRange m).map fromHead
    heads.reverse ++ (schedule m).map raised ++ (heads++tails).reverse

def instructions : (m : ℕ)→Layout m→List (Instruction m)
  | 0,_=>[]
  | m+1,L=>
    (headPlan (leading L)).reverse ++ (instructions m (lower L)).map raise ++
      ((headPlan (pivot L))++(tailPlan (other L))).reverse

theorem gates (m : ℕ) (L : Layout m) : (instructions m L).map Prod.fst=schedule m := by
  induction m with
  | zero=>rfl
  | succ m ih=>
    have f (q : List (Instruction m)) : (q.map raise).map Prod.fst=(q.map Prod.fst).map raised := by
      simp only [List.map_map];rfl
    simp only [instructions,schedule,List.map_append,List.map_reverse,f,ih]
    simp [headPlan,tailPlan,pins,List.map_map,Function.comp_def]

def controls {m : ℕ} (L : Layout m) := (instructions m L).map Prod.snd

theorem actual {m : ℕ} (L : Layout m) : (schedule m).zip (controls L)=instructions m L := by
  rw [←gates m L]
  unfold controls
  generalize instructions m L=q
  induction q with
  | nil=>rfl
  | cons a q ih=> simp only [List.map_cons,List.zip_cons_cons,Prod.mk.eta,ih]

theorem instructions_apply (m : ℕ) (L : Layout m) (x : Bits m) : applyList (instructions m L) x=L x := by
  induction m with
  | zero=>exact Subsingleton.elim _ _
  | succ m ih=>
    let V:=headPlan (leading L)
    let U:=headPlan (pivot L)++tailPlan (other L)
    let y:=applyList V.reverse x
    have left : applyList V y=x := by simpa only [y,List.reverse_reverse] using undo V.reverse x
    have lifted : applyList ((instructions m (lower L)).map raise) y=reduced L y := by
      calc
        _ = applyList ((instructions m (lower L)).map raise) (Fin.cons (y 0) (Fin.tail y)) :=
          congrArg _ (Fin.cons_self_tail y).symm
        _ = Fin.cons (y 0) (lower L (Fin.tail y)) := by rw [raised_apply,ih]
        _ = _ := (reduced_apply L y).symm
    have effect : reduced L y=applyList U (L x) := by
      change clean L (layout V y)=applyList U (L x)
      rw [layout_apply,left]
      change layout (tailPlan (other L)) (layout (headPlan (pivot L)) (L x))=applyList U (L x)
      rw [layout_apply,layout_apply,apply_append]
    change applyList (_++_++U.reverse) x=_
    rw [apply_append,apply_append]
    change applyList U.reverse (applyList ((instructions m (lower L)).map raise) y)=_
    rw [lifted,effect,undo]

theorem realizes {m : ℕ} (L : Layout m) (x : Bits m) :
    applyList ((schedule m).zip (controls L)) x = L x := by
  rw [actual,instructions_apply]

theorem realizes_inverse {m : ℕ} (L : Layout m) (x : Bits m) :
    applyList ((schedule m).zip (controls L)).reverse x=L.symm x := by
  have used:=undo ((schedule m).zip (controls L)) (L.symm x)
  simpa only [realizes,LinearEquiv.apply_symm_apply] using used

theorem length (m : ℕ) : 2*(schedule m).length=3*m*(m-1) := by
  induction m with
  | zero=>rfl
  | succ m ih=>
    simp only [schedule,List.length_append,List.length_reverse,List.length_map,List.length_finRange]
    cases m with
    | zero=>simp [schedule]
    | succ m=>simp only [Nat.succ_sub_one] at ih ⊢;nlinarith

theorem length_le (m : ℕ) : (schedule m).length≤3*m*m := by
  have eqn := length m
  have bound := Nat.mul_le_mul_left (3*m) (Nat.sub_le m 1)
  omega

/-- The authentic issued source row stores the coefficient of precisely this
single-coordinate transvection in its indicated little-endian bit. -/
theorem coefficient {m : ℕ} (L : Layout m) (i j : Fin m) :
    (rowIndex m (rowFunctional L i)).val / 2^j.val % 2 = (L (axis j) i).val := by
  let B:=Pi.basisFun (ZMod 2) (Fin m)
  let bits:=B.dualBasis.equivFun (rowFunctional L i)
  have inv:=congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply bits) j)
  change (finFunctionFinEquiv bits).val/2^j.val%2=(bits j).val at inv
  change (finFunctionFinEquiv bits).val/2^j.val%2=_
  rw [inv]
  apply congrArg ZMod.val
  calc
    bits j = rowFunctional L i (B j) := B.dualBasis_equivFun (rowFunctional L i) j
    _ = L (axis j) i := by
      simpa only [B,axis,Pi.basisFun_apply] using rowFunctional_apply L i (B j)

end Hierarchy.DescentGLNielsen

end
end OAI
