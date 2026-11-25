import OAI.Computability.IntegerMultiplication.Earth.Fire

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Earth
open Code Strip Strip.Dims Strip.Optic Loom Adic Net Net.Tensor Net.Walsh Packed Phase Haze
open Finset Matrix
variable {H K G N : ℕ} {J O U C R W : Type} [CommRing R]
variable [Fintype J] [DecidableEq J] [Fintype U] [DecidableEq U]
variable [Fintype C] [DecidableEq C] [Fintype O]
noncomputable section
abbrev bitK (x : Block 2 K) (i : Fin K) : B := (most x)[i.val]'(by simp)
def layBit (K : ℕ) : Block 2 K ≃ Addr (Fin K) :=
  Equiv.ofBijective bitK (Fintype.bijective_iff_injective_and_card _ |>.mpr
    ⟨fun x y e=> distinct _ _ (List.ext_getElem (by simp) (fun i hx hy=>congrFun (show bitK x=bitK y from e) ⟨i,by simpa using hx⟩)),
    by rw [Adic.count,Fintype.card_pi]; simp [B] ⟩)

def letter (i : Fin K) : Adopt (chunks i.val (K-i.val-1)) (line 2 K) :=
  (chord ..).thenDo (castN 2 _ _ (by unfold width; have := i.isLt; omega))
theorem let_r (i : Fin K) (x : Chunk (i:ℕ) (K-i.val-1)) :
    most ((letter i).cast x)=most x.1.1 ++ [x.1.2] ++ most x.2 := by
  change most ((castN 2 _ _ _).cast ((tile 2 _ _).cast ((flag _).cast x.1,x.2)))=_
  rw [castN_most,tile_most,flag_word]

theorem step_q (i : Fin K) (x) :
    (layBit K ((letter i).cast x)) i = (pulse x).1 := by
  change (most ((letter i).cast x))[i.val]=_
  simp only [let_r, List.append_assoc]
  rw [List.getElem_append_right (by simp)]
  simp
  rfl

-- unmodified indices
theorem step_right (i j : Fin K) (v : i≠j) (x y)
    (e : (pulse x).2=(pulse y).2) :
    (layBit K ((letter i).cast x)) j = (layBit K ((letter i).cast y)) j := by
  obtain ⟨⟨hx,l⟩,m⟩ := x
  obtain ⟨⟨y,a⟩,b⟩ := y
  change (hx,m)=(y,b) at e
  rcases Prod.ext_iff.mp e with ⟨rfl,rfl⟩
  change (most ((letter i).cast _))[j.val]=(most ((letter i).cast _))[j.val]
  simp only [let_r,List.append_assoc]
  rcases lt_or_gt_of_ne (show i.val≠j.val from fun f=> v (Fin.ext f)) with w|w
  · have e (s : Fin 2) (t : j.val<(most hx ++ ([s]++most m)).length) :
        (most hx ++ ([s]++most m))[j.val]'t=
        (most m)[j.val-i.val-1]'(by have := j.isLt; rw [Adic.length]; omega) := by
      rw [List.getElem_append_right (by simp; exact w.le)]
      rw [List.getElem_append_right (by simp only [List.length_cons,List.length_nil,Adic.length]; omega)]
      simp
    rw [e,e]
  have hB : j.val<(most hx).length := by simpa using w
  rw [List.getElem_append_left hB,List.getElem_append_left hB]
theorem office (i : Fin K) (x y : Chunk i.val (K-i.val-1)) :
    (pulse x).2=(pulse y).2 ↔ ∀ j:Fin K,j≠i →
    (layBit K ((letter i).cast x)) j=(layBit K ((letter i).cast y)) j := by
  refine ⟨fun e j h=> step_right i j (Ne.symm h) x y e, ?_⟩
  intro f
  let z : Chunk i.val (K-i.val-1) := pulse.symm ((pulse x).1,(pulse y).2)
  have zp : pulse z = ((pulse x).1,(pulse y).2) := Equiv.apply_symm_apply _ _
  suffices e : (layBit K ((letter i).cast x)) = (layBit K ((letter i).cast z)) by
    rw [(letter i).cast.injective ((layBit K).injective e),zp]
  funext j
  by_cases h : j=i
  · subst j; rw [step_q,step_q,zp]
  rw [f j h]
  apply step_right i j (Ne.symm h)
  rw [zp]

-- compatibility lemma with range filtering
variable (M : Tensor.Mat B R) (t : U↪J)
def color_r (i : J) : Bool := decide (i ∈ Finset.univ.map t)
def patch (f : J→Bool) : Tensor.Mat (Addr J) R :=
  mat (fun i=> if f i then M else 1)
omit [DecidableEq U] in
theorem parts (x y : Addr J) :
    patch M (color_r t) x y =
    (if ∀ j, j∉ Finset.univ.map t → x j=y j then mat (fun _ => M) (x ∘ t) (y ∘ t) else (0:R)) := by
  unfold patch; simp only [Tensor.app]
  classical
  let s := Finset.univ.map t
  calc
    _ = (∏ i∈ sᶜ,(if color_r t i then M else 1) (x i) (y i))*
        ∏ i∈ s,(if color_r t i then M else 1) (x i) (y i) :=
          (Finset.prod_compl_mul_prod s _).symm
    _ = _ := by
      have g (a) (v:a∈sᶜ) : (if color_r t a=true then M else 1) (x a) (y a) =
          (if x a=y a then 1 else 0) := by
        have e : color_r t a=false := by simp [color_r,show a∉ Finset.univ.map t from Finset.mem_compl.mp v]
        simp [e,Matrix.one_apply]
      rw [Finset.prod_congr rfl g, Finset.prod_map]
      have d' (u : U) :
          (fun i j=> (if color_r t (t u)=true then M else 1) i j) (x (t u)) (y (t u)) =
          M (x (t u)) (y (t u)) := by simp [color_r]
      have e : (fun i : U=> (if color_r t (t i)=true then M else 1) (x (t i)) (y (t i))) =
          (fun i : U=> M (x (t i)) (y (t i))) := funext d'
      rw [e]
      split
      next h =>
        rw [show (∏ j∈ sᶜ, if x j=y j then (1:R) else 0)=1 by
          apply Finset.prod_eq_one; intro j h'
          exact ite_eq_left (h _ (Finset.mem_compl.mp h'))]
        rw [one_mul]; rfl
      next h =>
        obtain ⟨j,e⟩ := not_forall.mp h
        rw [Classical.not_imp] at e
        rw [Finset.prod_eq_zero (Finset.mem_compl.mpr e.1) (ite_eq_right e.2),zero_mul]

-- relationship between parent and sub
variable {M} {U0 C0 : Type} [Fintype C0] [DecidableEq C0] -- parent lens with addresses Addr J
variable (A : Lens O (Addr J) C0) (D : Lens O (Addr U) C)
structure Expose (A : Lens O (Addr J) C0) (D : Lens O (Addr U) C) (t : U↪J) : Prop where
  land i : (D i).1=(A i).1 ∘ t
  keep x y : (D x).2=(D y).2 ↔ (A x).2=(A y).2 ∧ ∀ j,j∉Finset.univ.map t → (A x).1 j=(A y).1 j

theorem stretch (e : Expose A D t) (M : Tensor.Mat B R) :
    operate D (mat (fun _=>M)) = operate A (patch M (color_r t)) := by
  classical
  unfold operate
  rw [← Phase.align,← Phase.align]
  suffices v : (Phase.grid D (mat (fun _=>M))) = Phase.grid A (patch M (color_r t)) by rw [v]
  ext i j
  simp only [Phase.grid,Matrix.of_apply,parts,e.land]
  by_cases h : (A i).2=(A j).2 <;> simp [h,e.keep]

end
end Earth

end IntegerMultiplication
end Computability
end OAI
