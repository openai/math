import OAI.Computability.BorderVNP.PackedEncodedCellIncidence
import OAI.Computability.BorderVNP.PackedFinalCellTaggedGuard

/-! # The native cell guard classifies the true finite owner's staged physical term -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalCell

open Crossing CellAddresses CellSparse Diagonal.CellEntries
open scoped Classical

variable {D m np ns C : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
variable (N : Network D P bits) (cell : N.Site → Fin C) (c : Fin C)
variable (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin np)
variable (state : Site.Programs N) (owner : Fin ns → ℕ)
local notation3 "key" => fun v => (cell v).val
local notation3 "progs" => fun v => (state v).program
local notation3 "size" => fun v => (state v).program.size
local notation3 "widths" => FinalReports.bank_sizes N cell progs c

private def recast {s : Site} {x y : Fin s.incoming → Bool} {Param Gadget : Type*}
    {ok : (Fin s.work → Bool) → Prop} {tag : Entry Param Gadget} {num : Gadget ↪ ℕ}
    (eq : x=y) (h : s.TagRead y ok tag num) : s.TagRead x ok tag num where
  work := h.work
  observations := h.observations
  chosen := h.chosen
  read g os good := eq ▸ h.read g os good
  count := h.count

/-- Every site of the finite cell appears in its native sorted owner list. -/
theorem mem_sites_of_owner {V : Type} (id : V ↪ Fin ns) (owner : Fin ns → ℕ) (v : V) (c : ℕ) (atCell : owner (id v)=c) :
    v ∈ sites id owner c :=
  List.mem_filterMap.mpr ⟨id v,List.mem_filter.mpr ⟨List.mem_finRange _,by simp [atCell]⟩,Function.partialInv_left id.injective v⟩

/-- The actual merged directory reads the supplied, wire and site banks of the
original finite cell. Passing characterizes all its owned physical sites, even
when its public row list is empty or some site emits no observations. -/
theorem guarded_finite_tagged_iff {Param Gadget : Type*} (number : Gadget ↪ ℕ)
    (tag : N.Site → Entry Param Gadget) (compatible : (v : N.Site) → (Fin (state v).birth.work → Bool) → Prop)
    (g : Fin (guessedSize N cell c) → Bool) (a : Fin (siteSize N cell c size) → Bool) (x : Fin (suppliedSize N cell c) → Bool)
    (read : (v : {v : N.Site // cell v=c}) → (state v.val).birth.TagRead
      ((state v.val).retention.readInput (Placement.canonical N cell c edgeID portID v g x ∘ Fin.cast (state v.val).size))
      (compatible v.val) (tag v.val) number)
    (reports : List (List ℕ)) (ho : ∀ v, owner (siteID v)=(cell v).val)
    (birthLocal : ∀ v, (state v).birth.Local) (schema : ∀ v, (state v).program.Schema)
    (relative : ∀ v, (state v).program.RelativeBoxes)
    (selected : ∀ v : {v : N.Site // cell v=c}, compatible v.val ((state v.val).originalWord (siteWords N cell c siteID size a v)))
    (out : List (Bool × Option ℕ)) :
    let live := sites siteID owner c.val
    let obs := fun v : N.Site => if hv : cell v=c then (read ⟨v,hv⟩).observations else []
    (directory owner N key siteID edgeID portID progs c.val reports).guardedObservations
      (lookup (bank N cell c size g a x)) = some out ↔
      live.flatMap obs=out ∧ ∀ v : {v : N.Site // cell v=c},
        let inputs := Placement.canonical N cell c edgeID portID v g x ∘ Fin.cast (state v.val).size
        tag v.val ≠ 0 ∧ siteWords N cell c siteID size a v =
          Fin.append ((state v.val).retention.complete inputs (read v).work) inputs := by
  intro live obs
  let fromNat (v : {v : N.Site // key v=c.val}) : {v : N.Site // cell v=c} := ⟨v.val,Fin.ext v.property⟩
  let gn := g ∘ Fin.cast widths.1
  let xn := x ∘ Fin.cast widths.2.2
  let an := a ∘ Fin.cast widths.2.1
  let actual (v : {v : N.Site // cell v=c}) := Placement.canonical N cell c edgeID portID v g x ∘ Fin.cast (state v.val).size
  let native (v : {v : N.Site // key v=c.val}) := currentInput N key edgeID portID state c.val gn xn v
  have inputEq (v : {v : N.Site // key v=c.val}) : native v = actual (fromNat v) :=
    congrArg (· ∘ Fin.cast (state v.val).size) (FinalTies.canonical_nat N cell c progs edgeID portID (fromNat v) g x)
  let numRead (v : {v : N.Site // key v=c.val}) :=
    recast (congrArg (state v.val).retention.readInput (inputEq v)) (read (fromNat v))
  have siteEq (v : {v : N.Site // key v=c.val}) :
      siteWords N key c.val siteID size an v = siteWords N cell c siteID size a (fromNat v) :=
    FinalTies.siteWords_nat N cell c progs siteID a (fromNat v)
  have sel (v : {v : N.Site // key v=c.val}) :
      compatible v.val ((state v.val).originalWord (siteWords N key c.val siteID size an v)) := by
    rw [siteEq v]
    exact selected (fromNat v)
  have checked := guarded_tagged_iff N key siteID edgeID portID state owner c.val gn xn number tag compatible
    numRead reports ho birthLocal schema relative an sel out
  let chunks := fun v : N.Site => if hv : key v=c.val then (numRead ⟨v,hv⟩).observations else []
  have same : live.flatMap chunks=live.flatMap obs := by
    apply List.flatMap_congr
    intro v hv
    have he := (ho v).symm.trans (site_owner siteID owner hv)
    have eqn : cell v=c := Fin.ext he
    simp only [chunks,obs,dite_eq_left (show key v=c.val from he),dite_eq_left eqn]
    rfl
  have banks := FinalTies.bank_nat N cell c progs g a x
  change bank N key c.val size gn an xn=bank N cell c size g a x at banks
  constructor
  · intro returned
    obtain ⟨flat,all⟩ := checked.mp (banks ▸ returned)
    refine ⟨same.symm.trans flat,?_⟩
    intro v
    have hv := mem_sites_of_owner siteID owner v.val c.val ((ho v.val).trans (congrArg Fin.val v.property))
    let vn : {v : N.Site // key v=c.val} := ⟨v.val,congrArg Fin.val v.property⟩
    have one := all v.val hv
    change tag v.val≠0 ∧ siteWords N key c.val siteID size an vn =
      Fin.append ((state v.val).retention.complete (native vn) (read v).work) (native vn) at one
    rw [siteEq vn,inputEq vn] at one
    exact one
  · rintro ⟨flat,all⟩
    rw [← banks]
    apply checked.mpr
    refine ⟨same.trans flat,?_⟩
    intro v hv
    let vn : {v : N.Site // key v=c.val} := ⟨v,(ho v).symm.trans (site_owner siteID owner hv)⟩
    change tag v≠0 ∧ siteWords N key c.val siteID size an vn =
      Fin.append ((state v).retention.complete (native vn) (read (fromNat vn)).work) (native vn)
    rw [siteEq vn,inputEq vn]
    exact all (fromNat vn)

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI
