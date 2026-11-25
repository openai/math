import OAI.Hierarchy.DescentGadgetNetwork

namespace OAI
/-! # Exact open contraction of the selected physical motif graph -/

namespace Hierarchy.DescentSixParty.GadgetNetwork
open Computability.VPVNP Computability.VPVNP.WireTensor Computability.BorderVNP.Crossing
open ThreeFlat.Diagonal.MotifKernel
open scoped Classical BigOperators
noncomputable section
variable {I : Type} [Fintype I] {D : ℕ} {P : Type*} {bits : P → ℕ}
variable (N : Network D P bits) (pick : I × Fin 2 ↪ N.Edge)
variable {F : Type*} [Field F]

private theorem not_selected (e : N.Edge) :
    e∈(Finset.univ.map pick)ᶜ ↔ selected N pick e=none := by
  by_cases h : ∃t,pick t=e
  · obtain ⟨t,rfl⟩ := h
    simp
  · simp [selected,h,Finset.mem_map]

private def Consistent (head tail : N.Assignment) := ∀e∈(Finset.univ.map pick)ᶜ,head e=tail e

/-- The new destination arms parametrize exactly the right-side assignments
that agree on every unchanged cable with a given original left assignment. -/
private def consistentEquiv (head : N.Assignment) :
    Arms N pick ≃ {tail : N.Assignment // Consistent N pick head tail} where
  toFun arm := ⟨restore N pick head arm,fun e he =>
    (restore_none N pick head arm e ((not_selected N pick e).mp he)).symm⟩
  invFun tail := fun t=>tail.val (pick t)
  left_inv arm := funext (restore_pick N pick head arm)
  right_inv tail := by
    apply Subtype.ext
    funext e
    cases h : selected N pick e with
    | none =>
      exact (restore_none N pick head _ e h).trans (tail.property e ((not_selected N pick e).mpr h))
    | some t =>
      obtain rfl := (selected_spec N pick h).symm
      exact restore_pick N pick _ _ t

private theorem delta_consistent (head tail : N.Assignment) :
    (∏e∈(Finset.univ.map pick)ᶜ,delta (F:=F) N (head,tail) e) =
      if Consistent N pick head tail then 1 else 0 := by
  by_cases yes : Consistent N pick head tail
  · rw [ite_eq_left yes]
    exact Finset.prod_eq_one fun e he=>ite_eq_left (yes e he)
  · rw [ite_eq_right yes]
    change ¬∀e∈(Finset.univ.map pick)ᶜ,head e=tail e at yes
    push Not at yes
    obtain ⟨e,he,bad⟩ := yes
    exact Finset.prod_eq_zero he (ite_eq_right bad)

/-- Sum the actual arms and transfer them to the split-end representation.
A nonselected cable has only one physical word and contributes its equality
indicator when both original split indices are displayed. -/
theorem sum_arms (f : Ends N → F) :
    (∑head,∑arm : Arms N pick, f (head,restore N pick head arm)) =
      ∑ a : Ends N, (∏e∈(Finset.univ.map pick)ᶜ,delta N a e)*f a := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro head _
  rw [show (∑arm : Arms N pick,f (head,restore N pick head arm))=
    ∑ b : {tail // Consistent N pick head tail},f (head,b.val) from
      (consistentEquiv N pick head).sum_comp (fun b=>f (head,b.val))]
  rw [←Finset.sum_subtype (Finset.univ.filter (Consistent N pick head)) (by simp) (fun x=>f (head,x)),
    Finset.sum_filter]
  simp_rw [delta_consistent]
  simp only [ite_mul,one_mul,zero_mul]

variable (sw : I → Fin 8 → ℕ)
local notation "M" => physical N pick sw

abbrev Inner := (i : I) → (e : Fin 8) → Fin (2^(sw i e))

/-- Enumerate the unchanged physical words, the added destination arms,
and one independent eight-tuple of supply edge words for every occurrence. -/
def unpack : (M).Assignment ≃ N.Assignment × Arms N pick × Inner sw where
  toFun a := (fun e=>a (.inl e),fun t=>a (.inr (.inl t)),supplyWords N pick sw a)
  invFun t := fun
    | .inl e => t.1 e
    | .inr (.inl e) => t.2.1 e
    | .inr (.inr p) => (bitsFin _).symm (t.2.2 p.1 p.2)
  left_inv a := by
    funext e
    rcases e with e | (t | ⟨i,j⟩)
    · rfl
    · rfl
    · exact (bitsFin (sw i j)).symm_apply_apply _
  right_inv t := by
    rcases t with ⟨head,arm,inner⟩
    refine Prod.ext ?_ ?_
    · rfl
    refine Prod.ext ?_ ?_
    · rfl
    funext i e
    exact (bitsFin (sw i e)).apply_symm_apply _

variable (dw : I → ℕ) (fit : ∀i s,N.width (pick (i,s))=dw i)
variable (T : N.Tables F) (L : ∀ i j,(Demand (F:=F) dw i).Basis j → (Supply (F:=F) sw i).Basis j → F)

private theorem change_sum_instance {α : Type*} (f : α → F) (first second : Fintype α) :
    (∑ x ∈ @Finset.univ α first, f x) = ∑ x ∈ @Finset.univ α second, f x := by
  rw [Subsingleton.elim first second]

omit [Fintype I] in
private theorem grouped_raw (layout : Bool) (i : I) (a : Ends N) :
    groupedTerm (fun e=>Fin (2^(sw i e))) layout (L i) (demandInput N pick dw fit a i) =
      ∑y,∏j, L i j (demandInput N pick dw fit a i j) (edgeAssignment supplySrc supplyDst y j) := by
  exact (applyLocal_eq_grouped supplySrc supplyDst (cluster layout) (L i)
    (demandInput N pick dw fit a i)).symm.trans
      ((applyLocal_wireNetwork supplySrc supplyDst _ (L i) (demandInput N pick dw fit a i)).trans
        (change_sum_instance _ _ _))

/-- Every term in the powered certificate is itself the complete exposed tensor
of the explicit six-new-sites/eight-supply-wires network. This also covers
parallel original wires, loops, and empty selected batches. -/
theorem physical_value_eq_grouped (layout : Bool) (pins : Ports bits) :
    (M).value (tables N pick sw dw fit T L) pins =
      ∑ a : Ends N,untouched N T pick pins a *
        ∏i,groupedTerm (fun e=>Fin (2^(sw i e))) layout (L i) (demandInput N pick dw fit a i) := by
  let old (a : Ends N) := ∏v,splitRead N T pins a v
  let motif (a : Ends N) (i : I) (y : (e : Fin 8) → Fin (2^(sw i e))) :=
    ∏ j,L i j (demandInput N pick dw fit a i j) (edgeAssignment supplySrc supplyDst y j)
  let contracted (a : Ends N) := ∏i,∑ y,motif a i y
  have each (a : (M).Assignment) :
      (∏v,(M).read (tables N pick sw dw fit T L) a pins v) =
        old (ends N pick sw a) * ∏i,motif (ends N pick sw a) i (supplyWords N pick sw a i) := by
    let row : N.Site ⊕ (I × Fin 6) → F := (M).read (tables N pick sw dw fit T L) a pins
    change (∏v, row v) = _
    rw [Fintype.prod_sum_type row,Fintype.prod_prod_type (fun t => row (.inr t))]
    simp only [row,old_read,party_read,old,motif]
  have reordered := (unpack N pick sw).symm.sum_comp
    (fun a => old (ends N pick sw a) * ∏i,motif (ends N pick sw a) i (supplyWords N pick sw a i))
  calc
    _ = ∑a : (M).Assignment,old (ends N pick sw a) * ∏i,motif (ends N pick sw a) i (supplyWords N pick sw a i) :=
      Finset.sum_congr rfl fun a _=>each a
    _ = ∑head,∑arm : Arms N pick, old (head,restore N pick head arm)*contracted (head,restore N pick head arm) := by
      rw [←reordered,Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro head _
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro arm _
      rw [show contracted (head,restore N pick head arm)=
        ∑z : Inner sw,∏i,motif (head,restore N pick head arm) i (z i) from Fintype.prod_sum _,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      let a := (unpack N pick sw).symm (head,arm,z)
      have ends_eq : ends N pick sw a = (head, restore N pick head arm) := rfl
      have supply_eq : supplyWords N pick sw a = z :=
        congrArg (fun t : N.Assignment × Arms N pick × Inner sw => t.2.2)
          ((unpack N pick sw).apply_symm_apply (head,arm,z))
      change old (ends N pick sw a) * (∏ i, motif (ends N pick sw a) i (supplyWords N pick sw a i)) = _
      rw [ends_eq,supply_eq]
    _ = _ := by
      rw [sum_arms N pick (fun a => old a*contracted a)]
      apply Finset.sum_congr rfl
      intro a _
      simp only [untouched,grouped_raw N pick sw dw fit L,old,contracted,motif]
      ring

end
end Hierarchy.DescentSixParty.GadgetNetwork

end OAI
