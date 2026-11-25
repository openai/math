import OAI.Hierarchy.DescentTerminalRecordPadding
import OAI.Hierarchy.DescentRestrictedPrivateCount

namespace OAI
/-! # Distinct positive private words in the complete clipped native primitive record -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentTerminalChronologicalBooks DescentKernelHistory DescentTerminalRecipeRows
open scoped Classical BigOperators
noncomputable section
variable {q t H N A w : ℕ} (site : Site) (r : ∀v : Fin site.nodes,Recipe (Fin t) (Fin (site.arity v)))
    (birth : Birth r) (hH : ∀v,Fintype.card (r v).Hidden≤H) (hN : ∀v,Fintype.card (r v).Node≤N)
    (hA : ∀v j,(r v).arity j≤A) (hw : ∀v j,(r v).width j≤w) (short : ∀v,site.arity v≤q) (v : Fin site.nodes)
local notation "z" => record site r birth hH hN hA hw short v

theorem references_image :
    (Finset.univ.image (fun ij : Fin N×Fin A=>(value z (nodeArg ij.1 ij.2)).val)).filter (q<·)=
      Finset.univ.image (fun h : (r v).UsedWord=>q+(ordinal (birth.hidden v) h.val).val+1) := by
  classical
  ext k
  simp only [Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨⟨i,j⟩,rfl⟩,hi⟩
    change q<(value z (nodeArg i j)).val at hi
    have permitted : allows (fun key=>(value z key).val) (nodeArg i j) := by
      by_contra h
      have zero:=record_zeros site r birth hH hN hA hw short v (nodeArg i j) h
      omega
    change i.val<(value z nodeCount).val ∧ j.val<(value z (nodeArity i)).val at permitted
    have nodes:=(counts_read site r birth hH hN hA hw short v).2.2
    let index : Fin (Fintype.card (r v).Node):=⟨i.val,by omega⟩
    let u:=(ordinal (birth.atom v)).symm index
    have row : (ordinal (birth.atom v) u).castLE (hN v)=i :=
      congrArg (fun k : Fin (Fintype.card (r v).Node)=>k.castLE (hN v))
        ((ordinal (birth.atom v)).apply_symm_apply index)
    have ar:=(node_read site r birth hH hN hA hw short v u).2
    rw [row] at ar
    let a : Fin ((r v).arity u):=⟨j.val,by omega⟩
    have column : a.castLE (hA v u)=j:=Fin.ext rfl
    have read:=arg_read site r birth hH hN hA hw short v u a
    rw [row,column] at read
    cases ref : (r v).operand u a with
    | inl b=>
      simp only [ref,Sum.elim_inl] at read
      have lim:=short v;have:=b.isLt
      omega
    | inr h=>
      exact ⟨⟨h,u,a,ref⟩,by simpa [ref] using read.symm⟩
  · rintro ⟨h,rfl⟩
    obtain ⟨u,a,ref⟩:=h.property
    have read:=arg_read site r birth hH hN hA hw short v u a
    refine ⟨⟨((ordinal (birth.atom v) u).castLE (hN v),a.castLE (hA v u)),?_⟩,by omega⟩
    simpa [ref] using read

theorem references_card :
    ((Finset.univ.image (fun ij : Fin N×Fin A=>(value z (nodeArg ij.1 ij.2)).val)).filter (q<·)).card=
      Fintype.card (r v).UsedWord := by
  rw [references_image site r birth hH hN hA hw short v,Finset.card_image_of_injective,Finset.card_univ]
  intro a b eqn
  change q+((ordinal (birth.hidden v)) a.val).val+1=q+((ordinal (birth.hidden v)) b.val).val+1 at eqn
  apply Subtype.ext
  apply (ordinal (birth.hidden v)).injective
  apply Fin.ext
  omega

end
end Hierarchy.DescentTerminalVertexFields

end OAI
