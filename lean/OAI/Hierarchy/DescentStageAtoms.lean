import OAI.Hierarchy.DescentMatrixBirthLoad
import OAI.Hierarchy.DescentSelectedHubs
import OAI.Hierarchy.DescentRecordedBranch

namespace OAI
/-! # The actual retained atom list and the newly born six-party scalar rows -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing GadgetNetwork
open scoped Classical BigOperators
noncomputable section
variable {Atom I C : Type} [Fintype I] {d : ℕ} {P : Type} {bits : P→ℕ}
variable (N : Network d P bits) (pick : I×Fin 2 ↪ N.Edge) (layout : Bool) (pack : N.Site→C)

abbrev SiteFiber (v : Merged N pick layout pack) :=
  {u : N.Site // newSite N pick layout pack (.inl u)=v}
abbrev NewFiber (v : Merged N pick layout pack) :=
  {ij : I×Fin 6 // newSite N pick layout pack (.inr ij)=v}

def gather {S E : Type} [Fintype S] (r : S→List E) : List E :=
  Finset.univ.toList.flatMap r

theorem gather_length {S E : Type} [Fintype S] (r : S→List E) :
    (gather r).length=∑u,(r u).length := by
  unfold gather
  rw [List.length_flatMap]
  exact Finset.sum_map_toList Finset.univ (fun u => (r u).length)

variable (rec : N.Site→List Atom) {c : ℕ} (z : I→ℕ) (p : I→Profile c)
abbrev Record (Atom : Type) (c : ℕ) := Atom⊕(ℕ×Profile c×Fin 6)

/-- A record's index is intrinsic to its immutable gadget type. Old vertex
names and absolute pointers do not occur in the new field-table key. -/
def newRecords (v : Merged N pick layout pack) : List (Record Atom c) :=
  gather (fun u : SiteFiber N pick layout pack v=>(rec u.val).map Sum.inl) ++
  gather (fun t : NewFiber N pick layout pack v=>
    [Sum.inr (z t.val.1,p t.val.1,t.val.2)])

theorem newRecords_length (v : Merged N pick layout pack) :
    (newRecords N pick layout pack rec z p v).length=
      (∑u : SiteFiber N pick layout pack v,(rec u.val).length)+siteBirths N pick layout pack v := by
  simp [newRecords,gather_length,siteBirths,NewFiber]

theorem newRecords_total :
    (∑v,(newRecords N pick layout pack rec z p v).length)=
      (∑u,(rec u).length)+6*Fintype.card I := by
  simp_rw [newRecords_length,Finset.sum_add_distrib]
  apply congrArg₂ (·+·)
  · let loc := fun u : N.Site=>newSite N pick layout pack (.inl u)
    exact Fintype.sum_fiberwise loc (fun u => (rec u).length)
  · let loc := fun x : I×Fin 6=>newSite N pick layout pack (.inr x)
    change (∑v,Fintype.card {x // loc x=v})=_
    rw [←Fintype.card_sigma,Fintype.card_congr (Equiv.sigmaFiberEquiv loc),Fintype.card_prod,Fintype.card_fin,Nat.mul_comm]

theorem hub_empty (mark : Merged N pick layout pack→Bool)
    (old : ∀u,mark (newSite N pick layout pack (.inl u))=true→ rec u=[])
    (inserted : ∀ij,mark (newSite N pick layout pack (.inr ij))=false)
    {v : Merged N pick layout pack} (marked : mark v=true) :
    newRecords N pick layout pack rec z p v=[] := by
  apply List.length_eq_zero_iff.mp
  rw [newRecords_length]
  have noOld (u : SiteFiber N pick layout pack v) : rec u.val=[] :=
    old u.val (by rw [u.property]; exact marked)
  have empty : IsEmpty (NewFiber N pick layout pack v) :=
    ⟨fun t=>by have eq := inserted t.val;rw [t.property,marked] at eq;contradiction⟩
  let := empty
  simp [noOld,siteBirths]

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
