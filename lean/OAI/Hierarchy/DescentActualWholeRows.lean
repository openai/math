import OAI.Hierarchy.DescentNativeInputRow
import OAI.Hierarchy.DescentObservedReservations
import OAI.Hierarchy.DescentSharedRows

namespace OAI
/-! # Integer prefix fields for the literal fine terminal and paid rotor input -/

namespace Hierarchy.DescentChosenRouter.Dyadic
open DescentColonies DescentBaseProfile DescentOrderedWords DescentGL
open private label_injective from OAI.Hierarchy.DescentBadVolume
open scoped Classical BigOperators
noncomputable section
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] {k Y : ℕ} [NeZero Y]
variable (D : Dyadic V I k)

def baseSum (weight : V→Block k→ℕ) (v : V) (x : Block k) :=
  ∑i∈Finset.univ.filter (fun i : Block k=>i<x ∧
    group (D.b v) (rearrange D.L i)=group (D.b v) (rearrange D.L x)),weight v i

theorem baseOffset (weight : V→Block k→ℕ) (g : D.G) (o : D.OldAt g) :
    offset (D.blockKey g) (fun j=>weight j.val.1 j.val.2) o=baseSum D weight o.val.1 o.val.2 := by
  have matchBase {i : Block k} : baseOf D.b D.hk D.L (o.val.1,i)=g.val ↔
      group (D.b o.val.1) (rearrange D.L i)=group (D.b o.val.1) (rearrange D.L o.val.2) := by
    calc
      _ ↔ baseOf D.b D.hk D.L (o.val.1,i)=baseOf D.b D.hk D.L o.val :=
        ⟨fun h=>h.trans o.property.symm,fun h=>h.trans o.property⟩
      _ ↔ _ := by
        rw [←(label_injective D.b).eq_iff]
        simp [label,baseOf,layout_id]
  have loc (j : D.OldAt g): j.val.1=o.val.1 :=
    congrArg Sigma.fst (j.property.trans o.property.symm)
  unfold offset baseSum
  refine Finset.sum_bij (fun j _=>j.val.2) ?_ ?_ ?_ ?_
  · intro j before
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp before).2,matchBase.mp ?_⟩
    have pair : (o.val.1,j.val.2)=j.val := Prod.ext (loc j).symm rfl
    rw [pair]
    exact j.property
  · intro j _ t _ eqn
    exact (D.blockKey g).injective eqn
  · intro i hi
    obtain ⟨lt,mem⟩:=(Finset.mem_filter.mp hi).2
    exact ⟨⟨(o.val.1,i),matchBase.mpr mem⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt⟩,rfl⟩
  · intro j _
    rw [loc j]

theorem row_numeral {B S unit c : ℝ} (loads : D.Loads Y B S unit) (pos : 0<S) (pu : 0<unit)
    (ub : unit≤B) (ys : (Y:ℝ)*B≤S) (hc : 0<c) (scale : ℕ) (pay : S=(scale:ℝ)/c)
    (weight : V→Block k→ℕ) (known : ∀s o,loads.weight s o=(weight o.1 o.2:ℝ)/c)
    (s : Bool) (o : V×Block k) (ready : baseOf D.b D.hk D.L o∉validBases D.b D.keys ∧ ¬D.hub o.1) :
    (D.row loads pos pu ub ys s o).val=min (Y*(baseSum D weight o.1 o.2)/(2*scale)) (Y-1) := by
  let g : D.G:=⟨baseOf D.b D.hk D.L o,ready⟩
  let i : D.OldAt g:=⟨o,rfl⟩
  unfold Dyadic.row
  rw [dite_eq_left ready]
  change (Cumulative.row (Y:=Y) (D.blockKey g) (fun j=>loads.weight s j.val) S i).val=_
  simp_rw [known]
  rw [pay,Cumulative.natural_row_scaled (D.blockKey g) (fun j=>weight j.val.1 j.val.2) c hc,
    D.baseOffset weight g i]

end
end Hierarchy.DescentChosenRouter.Dyadic

namespace Hierarchy.DescentFineTerminals
open DescentColonies DescentBaseProfile DescentOrderedWords DescentGL
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {k D f B Y : ℕ} [NeZero Y]
variable (near : V→Finset V) (wt : V→Block k→ℕ) (room : ∀v x,wt v x≤B) (b : V→ℕ)
local notation "leafAt" => leafKey (D:=D) (f:=f) near wt room b

def leafSum (v : V) (x : Block k) := ∑y∈Finset.univ.filter (fun y : Block k=>y<x ∧ leafAt v y=leafAt v x),wt v y

omit [Fintype V] [DecidableEq V] in
theorem leaf_numeral (enough : Y≤2^f) (v : V) (x : Block k) :
    (row (D:=D) near wt room b enough (v,x)).val=
      min (Y*leafSum (D:=D) (f:=f) near wt room b v x/(2*(2^f*B))) (Y-1) := by
  let p:=leafAt v x
  let items:=occupants (D:=D) (f:=f) near wt room b v p
  let i : ↥items:=⟨x,occupant_mem near wt room b v x⟩
  have taken : offset (Function.Embedding.subtype (fun a=>a∈items)) (fun a=>wt v a.val) i=
      leafSum (D:=D) (f:=f) near wt room b v x := by
    unfold offset leafSum
    apply Finset.sum_bij (fun a _=>a.val)
    · intro a h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2,(Finset.mem_filter.mp a.property).2⟩
    · exact fun a _ b _ eqn=>Subtype.ext eqn
    · intro a h
      obtain ⟨lt,same⟩:=(Finset.mem_filter.mp h).2
      exact ⟨⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,same⟩⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt⟩,rfl⟩
    · exact fun _ _=>rfl
  have known := Cumulative.natural_row_scaled (Y:=Y) (Function.Embedding.subtype (fun a=>a∈items))
    (fun a=>wt v a.val) 1 zero_lt_one (2^f*B) i
  change (Cumulative.row (Y:=Y) (Function.Embedding.subtype (fun a=>a∈items))
    (fun a=>(wt v a.val:ℝ)) ((2^f*B:ℕ):ℝ) i).val=_
  simpa only [div_one,taken] using known

end
end Hierarchy.DescentFineTerminals

end OAI
