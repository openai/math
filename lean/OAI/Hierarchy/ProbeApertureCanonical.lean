import OAI.Hierarchy.ProbeAperturePackedChord

namespace OAI
/-! # The same fixed packer with explicit zero guards for all padded private bits -/

noncomputable section
namespace Hierarchy.Probe.ApertureCompactor
open ThreeFlat Routing Routing.StableCompaction
open Diagonal TraceCircuit TraceWords MotifSelectorChecks
open Computability.VPVNP.BurstRAM
open Tagged.WidePadding
open scoped Classical BigOperators Fin.CommRing
variable {n d b : ℕ}

abbrev Guards (n d b : ℕ) := Fin (Size n d b) ⊕ Unit

def guard (n d b : ℕ) : Ports (Guards n d b) (n*d) b where
  col i := ((ApertureMask.col i).val:Word b)
  live _:=.inr ()
  width i j:=.inl ((finProdFinEquiv (ApertureMask.role i,j)).castAdd _)
  payload i:=.inl (Fin.natAdd (n*b) (i.castAdd _))

def guardWires : Fin (Fintype.card (Guards n d b))→BitSource 0 (Size n d b) :=
  fun t=>match (Fintype.equivFin _).symm t with | .inl i=>.pin i | .inr _=>.constant true

def stage (F : Type*) [CommRing F] (n d b : ℕ) : Bool → Component F 0 (Size n d b)
  | false=>⟨_,network F n d b,BitSource.pin⟩
  | true=>⟨_,(guard n d b).network (F:=F),guardWires⟩

def strict (F : Type*) [CommRing F] (n d b : ℕ) : BitNetwork F (Size n d b) :=
  BitNetwork.glue (fun i=>(stage F n d b i).net) (fun i=>(stage F n d b i).wire)

def canonical (width : Fin n→ℕ) (x : Fin (n*d)→Bool) : Prop :=
  ∀i,x i=true → (ApertureMask.col i).val<width (ApertureMask.role i)

private theorem guard_at (width : Fin n→ℕ) (x y : Fin (n*d)→Bool) (h : Fin 0→Bool) :
    (fun j=>(guardWires (n:=n) (d:=d) (b:=b) j).read h (pins width x y))=
      (Sum.elim (pins (b:=b) width x y) (fun _ : Unit=>true)) ∘ (Fintype.equivFin (Guards n d b)).symm := by
  funext j
  cases hj:(Fintype.equivFin (Guards n d b)).symm j <;> simp [guardWires,hj,BitSource.read]

theorem strict_eval (F : Type*) [CommRing F] (width : Fin n→ℕ) (small : ∀i,width i≤d)
    (room : d<2^b) (x y : Fin (n*d)→Bool) :
    (strict F n d b).eval (pins width x y)=if canonical width x ∧ y=compact (ApertureMask.mask width) x then 1 else 0 := by
  let v:=Sum.elim (pins (b:=b) width x y) (fun _ : Unit=>true)
  have rd (i : Fin (n*d)) (j : Fin b) : v ((guard n d b).width i j)=bits (width (ApertureMask.role i):Word b) j := by
    simp [v,guard,pins,blocks_at]
  have pad:=(guard n d b).eval (F:=F) v (fun i=>(width (ApertureMask.role i):Word b)) rd
  have ok : (∀i,v ((guard n d b).payload i)=true →
      v ((guard n d b).live i)=true ∧ (guard n d b).col i<(width (ApertureMask.role i):Word b)) ↔ canonical width x := by
    simp only [v,guard,pins,Fin.append_left,Fin.append_right,Sum.elim_inl,Sum.elim_inr,true_and,canonical]
    simp only [Fin.lt_def,Fin.val_cast_of_lt ((ApertureMask.col _).isLt.trans room),
      Fin.val_cast_of_lt ((small _).trans_lt room)]
  rw [strict,BitNetwork.glue_eval,Fintype.sum_unique,Fintype.prod_bool]
  change ((guard n d b).network (F:=F)).eval
    (fun j=>(guardWires (n:=n) (d:=d) (b:=b) j).read
      (@default (Fin 0 → Bool) Unique.instInhabited) (pins width x y)) *
    (network F n d b).eval (pins width x y) = _
  rw [guard_at]
  change TypedWiring.value ((guard n d b).network (F:=F)) v * (network F n d b).eval (pins width x y)=_
  rw [pad,if_congr ok rfl rfl,eval F _ _ _ small room]
  split_ifs <;> simp_all

theorem strict_cost (F : Type*) [CommRing F] (n d b : ℕ) :
    (strict F n d b).cells+(strict F n d b).internal≤
      n*d*(200*b+65)+(n*d+n*d*(500*b+501)+128000*(n*d+1)*(Nat.log 2 (n*d+1)+2)^3) := by
  have h:=(guard n d b).cost (F:=F)
  have a:=cost F n d b
  simp only [strict,BitNetwork.glue_cells,BitNetwork.glue_internal,Fintype.sum_bool,stage]
  omega

theorem compact_injective (width : Fin n→ℕ) {x y : Fin (n*d)→Bool}
    (cx : canonical width x) (cy : canonical width y)
    (same : compact (ApertureMask.mask width) x=compact (ApertureMask.mask width) y) : x=y := by
  funext i
  by_cases used : (ApertureMask.col i).val<width (ApertureMask.role i)
  · let M:=ApertureMask.mask (d:=d) width
    have live : M i=true:=decide_eq_true used
    let j : Fin (n*d):=⟨prefixCount M i,(prefixCount_lt_card live).trans_le
      ((active M).card_le_univ.trans_eq (Fintype.card_fin _))⟩
    have eq:=congrFun same j
    rw [compact_at_prefixCount _ _ live (show j.val=prefixCount M i from rfl),
      compact_at_prefixCount _ _ live (show j.val=prefixCount M i from rfl)] at eq
    exact eq
  · cases hx:x i <;> cases hy:y i <;> simp_all [cx i,cy i]

theorem sum_output (F : Type*) [CommRing F] (width : Fin n→ℕ) (small : ∀i,width i≤d)
    (room : d<2^b) (x : Fin (n*d)→Bool) (φ : (Fin (n*d)→Bool)→F) :
    (∑y,(strict F n d b).eval (pins width x y)*φ y)=
      if canonical width x then φ (compact (ApertureMask.mask width) x) else 0 := by
  by_cases clean : canonical width x <;> simp [strict_eval F width small room,clean]

theorem sum_input (F : Type*) [CommRing F] (width : Fin n→ℕ) (small : ∀i,width i≤d)
    (room : d<2^b) (x : Fin (n*d)→Bool) (clean : canonical width x) (φ : (Fin (n*d)→Bool)→F) :
    (∑y,(strict F n d b).eval (pins width y (compact (ApertureMask.mask width) x))*φ y)=φ x := by
  have unique (y : Fin (n*d)→Bool) : (canonical width y ∧
      compact (ApertureMask.mask width) x=compact (ApertureMask.mask width) y) ↔ y=x := by
    constructor
    · rintro ⟨cy,h⟩;exact (compact_injective width clean cy h).symm
    · rintro rfl;exact ⟨clean,rfl⟩
  simp [strict_eval F width small room,unique]

end Hierarchy.Probe.ApertureCompactor
end

end OAI
