import OAI.Hierarchy.TaggedWireSettledLayout
import OAI.Hierarchy.ProbeRouteOccurrences

namespace OAI
/-! # Native occurrence order for permanent edges and both settlement directories -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe SettledMatrix
open scoped Classical

variable {K edges r : ℕ} {I C : Type} [Fintype I] [Fintype C]

def orientedIndex {E : Type} (a b : Fin K) (xs : List E) : Fin xs.length ≃ Fin (oriented a b xs).length :=
  if h : a<b then finCongr (by simp [oriented,h]) else Fin.revPerm.trans (finCongr (by simp [oriented,h]))

theorem oriented_get {E : Type} (a b : Fin K) (xs : List E) (i : Fin xs.length) :
    (oriented a b xs).get (orientedIndex a b xs i)=xs.get i := by
  by_cases h:a<b
  · have index : (orientedIndex a b xs i).val=i.val := by rw [orientedIndex,dite_eq_left h]; rfl
    simp only [List.get_eq_getElem,oriented,ite_eq_left h]
    exact getElem_congr_idx index
  · have index : (orientedIndex a b xs i).val=(Fin.rev i).val := by rw [orientedIndex,dite_eq_right h]; rfl
    have value : xs.length-1-(Fin.rev i).val=i.val := by
      change xs.length-1-(xs.length-(i.val+1))=i.val
      have := i.isLt
      omega
    simp only [List.get_eq_getElem,oriented,ite_eq_right h,List.getElem_reverse]
    exact getElem_congr_idx ((congrArg (fun q:ℕ=>xs.length-1-q) index).trans value)

namespace SettledMatrix.Layout
variable (B : SettledMatrix.Layout K edges I C)

def occurrences : Fin edges ⊕ RouteOccurrence B.core B.center ≃ Σi:Source edges I C,Fin (B.steps i).length where
  toFun
    | .inl i=>⟨.inl i,⟨0,by change 0<1;decide⟩⟩
    | .inr (.inl ⟨i,j⟩)=>⟨.inr (.inl i),orientedIndex (B.goods.tail i) (B.goods.head i) (B.core i) j⟩
    | .inr (.inr ⟨c,j⟩)=>⟨.inr (.inr c),orientedIndex (B.reserve.tail c) (B.reserve.head c) (B.center c) j⟩
  invFun
    | ⟨.inl i,_⟩=>.inl i
    | ⟨.inr (.inl i),j⟩=>.inr (.inl ⟨i,(orientedIndex (B.goods.tail i) (B.goods.head i) (B.core i)).symm j⟩)
    | ⟨.inr (.inr c),j⟩=>.inr (.inr ⟨c,(orientedIndex (B.reserve.tail c) (B.reserve.head c) (B.center c)).symm j⟩)
  left_inv := by
    rintro (i|⟨i,j⟩|⟨c,j⟩) <;> simp
  right_inv := by
    rintro ⟨(i|i|c),j⟩
    · exact Sigma.ext rfl (heq_of_eq (Subsingleton.elim (α:=Fin 1) 0 j))
    · exact congrArg (fun u : Fin (B.steps (.inr (.inl i))).length=>
        Sigma.mk (β:=fun z : Source edges I C=>Fin (B.steps z).length) (.inr (.inl i)) u)
        ((orientedIndex (B.goods.tail i) (B.goods.head i) (B.core i)).apply_symm_apply j)
    · exact congrArg (fun u : Fin (B.steps (.inr (.inr c))).length=>
        Sigma.mk (β:=fun z : Source edges I C=>Fin (B.steps z).length) (.inr (.inr c)) u)
        ((orientedIndex (B.reserve.tail c) (B.reserve.head c) (B.center c)).apply_symm_apply j)

def nativeOrder (enum : Fin r≃RouteOccurrence B.core B.center) :
    Fin (edges+r)≃Σi,Fin (B.routes i).length :=
  finSumFinEquiv.symm.trans <| (Equiv.sumCongr (Equiv.refl _) enum).trans <|
    B.occurrences.trans (Equiv.sigmaCongrLeft (β:=fun i=>Fin (B.steps i).length) numbered).symm

def nativeEdge (enum : Fin r≃RouteOccurrence B.core B.center) (i : Fin (edges+r)) : Fin edges :=
  Sum.elim id RouteOccurrence.edge ((Equiv.sumCongr (Equiv.refl _) enum) (finSumFinEquiv.symm i))

def nativeWidth (enum : Fin r≃RouteOccurrence B.core B.center)
    (fixed : Fin edges→ℕ) (stock : I→ℕ) (reserved used : C→ℕ) (i : Fin (edges+r)) : ℕ :=
  Sum.elim fixed (RouteOccurrence.weight stock reserved used)
    ((Equiv.sumCongr (Equiv.refl _) enum) (finSumFinEquiv.symm i))

omit [Fintype I] [Fintype C] in
theorem occurrence_edge (i : Fin edges ⊕ RouteOccurrence B.core B.center) :
    (B.steps (B.occurrences i).1).get (B.occurrences i).2=Sum.elim id RouteOccurrence.edge i := by
  rcases i with i|⟨i,j⟩|⟨c,j⟩
  · rfl
  · exact oriented_get _ _ _ _
  · exact oriented_get _ _ _ _

theorem native_edge (enum : Fin r≃RouteOccurrence B.core B.center) (i : Fin (edges+r)) :
    (B.routes (B.nativeOrder enum i).1).get (B.nativeOrder enum i).2=B.nativeEdge enum i := by
  let z := ((Equiv.sumCongr (Equiv.refl _) enum) (finSumFinEquiv.symm i))
  let rename := Equiv.sigmaCongrLeft (β:=fun i=>Fin (B.steps i).length) numbered
  have same := congrArg (fun p : Σ i,Fin (B.steps i).length=>(B.steps p.1).get p.2)
    (rename.apply_symm_apply (B.occurrences z))
  exact same.trans (B.occurrence_edge z)

theorem native_width (enum : Fin r≃RouteOccurrence B.core B.center) (fixed : Fin edges→ℕ)
    (stock : I→ℕ) (reserved used : C→ℕ) (i : Fin (edges+r)) :
    bits fixed stock reserved used (B.nativeOrder enum i).1=B.nativeWidth enum fixed stock reserved used i := by
  let z := ((Equiv.sumCongr (Equiv.refl _) enum) (finSumFinEquiv.symm i))
  let rename := Equiv.sigmaCongrLeft (β:=fun i=>Fin (B.steps i).length) numbered
  have same := congrArg (fun p : Σ i,Fin (B.steps i).length=>available fixed stock reserved used p.1)
    (rename.apply_symm_apply (B.occurrences z))
  refine same.trans ?_
  change available fixed stock reserved used (B.occurrences z).1=Sum.elim fixed (RouteOccurrence.weight stock reserved used) z
  rcases z with i|⟨i,j⟩|⟨c,j⟩ <;> rfl

end SettledMatrix.Layout
end Hierarchy.WireTelescope

end
end OAI
