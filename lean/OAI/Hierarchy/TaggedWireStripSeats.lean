import Mathlib.Data.Fin.Embedding
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

namespace OAI
/-! # Fixed role and boundary seats of one installed strip packet -/

noncomputable section
namespace Hierarchy.WireTelescope.StripPaths

open scoped Classical

variable {Role Link V : Type*}

abbrev Boundary (route : Role → List Link) := (i : Role) × Fin ((route i).length+1)

private def coordinates (route : Role → List Link) (short : ∀ i, (route i).length ≤ 2) :
    Boundary route ↪ Role × Fin 3 where
  toFun x := (x.1, ⟨x.2.val,lt_of_lt_of_le x.2.isLt (Nat.succ_le_succ (short x.1))⟩)
  inj' := by
    rintro ⟨i,j⟩ ⟨i',j'⟩ same
    have roles : i=i' := congrArg (fun p : Role × Fin 3 => p.1) same
    subst i'
    have ord : j.val=j'.val := congrArg (fun p : Role × Fin 3 => p.2.val) same
    exact Sigma.ext rfl (heq_of_eq (Fin.ext ord))

/-- Native shelf layout for the decoder on an already numbered public role menu. -/
def positionSeat {n : ℕ} (route : Fin n → List Link) (short : ∀ i, (route i).length ≤ 2) :
    Boundary route ↪ Fin (n*3) :=
  (coordinates route short).trans finProdFinEquiv.toEmbedding

theorem positionSeat_apply {n : ℕ} (route : Fin n → List Link) (short : ∀ i, (route i).length ≤ 2)
    (i : Fin n) (j : Fin ((route i).length+1)) :
    positionSeat route short ⟨i,j⟩ =
      finProdFinEquiv (i,(⟨j.val,lt_of_lt_of_le j.isLt (Nat.succ_le_succ (short i))⟩ : Fin 3)) := rfl

theorem positionSeat_decode {n : ℕ} (route : Fin n → List Link) (short : ∀ i, (route i).length ≤ 2)
    (i : Fin n) (j : Fin ((route i).length+1)) :
    finProdFinEquiv.symm (positionSeat route short ⟨i,j⟩) =
      (i,(⟨j.val,lt_of_lt_of_le j.isLt (Nat.succ_le_succ (short i))⟩ : Fin 3)) :=
  finProdFinEquiv.symm_apply_apply _

/-- Three persistent seats per role. The last coordinate is the literal
boundary index in the installed walk, including the initial and final ones. -/
def boundarySeat [Fintype Role] (order : Fin (Fintype.card Role) ≃ Role)
    (route : Role → List Link) (short : ∀ i, (route i).length ≤ 2) :
    Boundary route ↪ Fin (3*Fintype.card Role) :=
  (coordinates route short).trans (((order.symm.prodCongr (Equiv.refl (Fin 3))).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm _ _)))).toEmbedding)

theorem boundarySeat_val [Fintype Role] (order : Fin (Fintype.card Role) ≃ Role)
    (route : Role → List Link) (short : ∀ i, (route i).length ≤ 2) (x : Boundary route) :
    (boundarySeat order route short x).val = 3*(order.symm x.1).val+x.2.val :=
  Nat.add_comm _ _

/-- Taking the live boundaries at one site keeps the same numerical addresses.
The predicate can include both the site test and a positive role width. -/
def siteSeat [Fintype Role] (order : Fin (Fintype.card Role) ≃ Role)
    (route : Role → List Link) (short : ∀ i, (route i).length ≤ 2) (liveAt : Boundary route → Prop) :
    {x // liveAt x} ↪ Fin (3*Fintype.card Role) :=
  (Function.Embedding.subtype liveAt).trans (boundarySeat order route short)

theorem siteSeat_val [Fintype Role] (order : Fin (Fintype.card Role) ≃ Role)
    (route : Role → List Link) (short : ∀ i, (route i).length ≤ 2) (liveAt : Boundary route → Prop)
    (x : {x // liveAt x}) :
    (siteSeat order route short liveAt x).val = 3*(order.symm x.val.1).val+x.val.2.val :=
  boundarySeat_val order route short x.val

theorem site_card [Fintype Role] (order : Fin (Fintype.card Role) ≃ Role)
    (route : Role → List Link) (short : ∀ i, (route i).length ≤ 2) (liveAt : Boundary route → Prop) :
    Fintype.card {x // liveAt x} ≤ 3*Fintype.card Role := by
  simpa using Fintype.card_le_of_embedding (siteSeat order route short liveAt)

/-- The two endpoints of a physical role are distinct. At least one of them
misses any specified site, so at most two of the three boundaries can visit it. -/
theorem visit_count {len : ℕ} (visit : Fin (len+1) → V) (short : len ≤ 2)
    (apart : visit 0 ≠ visit (Fin.last len)) (s : V) :
    Fintype.card {j // visit j=s} ≤ 2 := by
  have miss : ∃ j, visit j ≠ s := by
    by_cases h : visit 0 = s
    · exact ⟨Fin.last len,fun last => apart (h.trans last.symm)⟩
    · exact ⟨0,h⟩
  obtain ⟨j,hj⟩ := miss
  have small := Fintype.card_subtype_lt (p:=fun j => visit j=s) (x:=j) hj
  rw [Fintype.card_fin] at small
  omega

/-- A fixed finite menu pays the largest three-seat role catalogue once. -/
def menuRoom {T : Type*} [Fintype T] (roles : T → Type*) [∀ t,Fintype (roles t)] :=
  Finset.univ.sup (fun t => 3*Fintype.card (roles t))

theorem menuRoom_bound {T : Type*} [Fintype T] (roles : T → Type*) [∀ t,Fintype (roles t)] (t : T) :
    3*Fintype.card (roles t) ≤ menuRoom roles :=
  Finset.le_sup (f := fun x => 3*Fintype.card (roles x)) (Finset.mem_univ t)

def menuSeat {T : Type*} [Fintype T] (roles : T → Type*) [∀ t,Fintype (roles t)] (t : T)
    (order : Fin (Fintype.card (roles t)) ≃ roles t) (route : roles t → List Link)
    (short : ∀ i, (route i).length ≤ 2) (liveAt : Boundary route → Prop) :
    {x // liveAt x} ↪ Fin (menuRoom roles) :=
  (siteSeat order route short liveAt).trans (Fin.castLEEmb (menuRoom_bound roles t))

theorem menuSeat_val {T : Type*} [Fintype T] (roles : T → Type*) [∀ t,Fintype (roles t)] (t : T)
    (order : Fin (Fintype.card (roles t)) ≃ roles t) (route : roles t → List Link)
    (short : ∀ i, (route i).length ≤ 2) (liveAt : Boundary route → Prop) (x : {x // liveAt x}) :
    (menuSeat roles t order route short liveAt x).val = 3*(order.symm x.val.1).val+x.val.2.val :=
  siteSeat_val order route short liveAt x

end Hierarchy.WireTelescope.StripPaths

end
end OAI
