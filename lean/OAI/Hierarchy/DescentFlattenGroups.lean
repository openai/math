import OAI.Hierarchy.DescentCommonGroups
import OAI.Hierarchy.DescentPackMass

namespace OAI
/-! # Moving the old group digits into the reset block coordinate -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentHostDirectory DescentColonies
open scoped Classical
noncomputable section
variable {P J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k m : ℕ} {bits : P→ℕ} (N : Network d P bits) (atSite : N.Site→J×V) (old : N.Site→Block k)
variable (digits : Block m ≃ J×Block k)
def filled (u : N.Site) : Block m := digits.symm ((atSite u).1,old u)

omit [Fintype J] [Fintype V] in
theorem filled_mass (load : N.Site→ℕ) (v : V) (x : Block m) :
    blockMass N (fun u=>(atSite u).2) (filled N atSite old digits) load v x=
      blockMass N atSite old load ((digits x).1,v) (digits x).2 := by
  unfold blockMass
  apply Finset.sum_congr rfl
  intro u _
  have cond : (atSite u).2=v ∧ filled N atSite old digits u=x ↔
      atSite u=((digits x).1,v) ∧ old u=(digits x).2 := by
    constructor
    · rintro ⟨host,h⟩
      have parts : ((atSite u).1,old u)=digits x := by
        simpa [filled] using congrArg digits h
      exact ⟨Prod.ext (congrArg (fun z : J × Block k => z.1) parts) host,
        congrArg (fun z : J × Block k => z.2) parts⟩
    · rintro ⟨host,block⟩
      refine ⟨congrArg (fun z : J × V => z.2) host,digits.injective ?_⟩
      have pairEq : ((atSite u).1,old u) = digits x :=
        Prod.ext (congrArg (fun z : J × V => z.1) host) block
      simpa only [filled,Equiv.apply_symm_apply] using pairEq
  simp only [cond]

omit [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] in
theorem filled_edges (near : V→Finset V)
    (edges : ∀e,atSite (N.dst e)∈groupedNear near (atSite (N.src e)))
    (same : ∀e,old (N.src e)=old (N.dst e)) (e : N.Edge) :
    filled N atSite old digits (N.src e)=filled N atSite old digits (N.dst e) ∧
    (atSite (N.dst e)).2∈near (atSite (N.src e)).2 := by
  obtain ⟨v,nearby,eqn⟩ := Finset.mem_map.mp (edges e)
  have lifted : ((atSite (N.src e)).1,v) = atSite (N.dst e) := eqn
  have group := congrArg (fun z : J × V => z.1) lifted
  have vertex := congrArg (fun z : J × V => z.2) lifted
  exact ⟨congrArg digits.symm (Prod.ext group (same e)),vertex ▸ nearby⟩

end
end Hierarchy.DescentSixParty.StarKeys

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentHostDirectory DescentColonies
open scoped Classical
noncomputable section
variable {P J E V : Type} [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
    {d k m : ℕ} {bits : P→ℕ} (N : Network d P bits) (atSite : N.Site→J×V) (old : N.Site→Block k)
variable (layout : J×Block k≃E×Block m)

def remainderPosition (u : N.Site) : E×V := ((layout ((atSite u).1,old u)).1,(atSite u).2)
def remainderBlock (u : N.Site) : Block m := (layout ((atSite u).1,old u)).2

omit [Fintype J] [Fintype E] [Fintype V] in
/-- An outer tensor-power index of arbitrary cardinality may be retained
while the power-of-two factors move into the actual reset block. -/
theorem remainder_mass (load : N.Site→ℕ) (v : E×V) (b : Block m) :
    blockMass N (remainderPosition N atSite old layout) (remainderBlock N atSite old layout) load v b=
      blockMass N atSite old load ((layout.symm (v.1,b)).1,v.2) (layout.symm (v.1,b)).2 := by
  unfold blockMass
  apply Finset.sum_congr rfl
  intro u _
  have cond : remainderPosition N atSite old layout u=v ∧ remainderBlock N atSite old layout u=b ↔
      atSite u=((layout.symm (v.1,b)).1,v.2) ∧ old u=(layout.symm (v.1,b)).2 := by
    constructor
    · rintro ⟨p,c⟩
      have addr : layout ((atSite u).1,old u)=(v.1,b) := Prod.ext (congrArg (fun z : E × V => z.1) p) c
      have raw := (layout.symm_apply_eq.mpr addr.symm).symm
      exact ⟨Prod.ext (congrArg (fun z : J × Block k => z.1) raw) (congrArg (fun z : E × V => z.2) p),
        congrArg (fun z : J × Block k => z.2) raw⟩
    · rintro ⟨p,c⟩
      have raw : ((atSite u).1,old u)=layout.symm (v.1,b) := Prod.ext (congrArg (fun z : J × V => z.1) p) c
      have done := layout.eq_symm_apply.mp raw
      exact ⟨Prod.ext (congrArg (fun z : E × Block m => z.1) done) (congrArg (fun z : J × V => z.2) p),congrArg (fun z : E × Block m => z.2) done⟩
  simp only [cond]

omit [Fintype J] [DecidableEq J] [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V] in
theorem remainder_edges (near : V→Finset V)
    (edge : ∀e,atSite (N.dst e)∈groupedNear near (atSite (N.src e)))
    (same : ∀e,old (N.src e)=old (N.dst e)) (e : N.Edge) :
    remainderBlock N atSite old layout (N.src e)=remainderBlock N atSite old layout (N.dst e) ∧
    remainderPosition N atSite old layout (N.dst e)∈groupedNear near (remainderPosition N atSite old layout (N.src e)) := by
  obtain ⟨v,close,p⟩ := Finset.mem_map.mp (edge e)
  have lifted : ((atSite (N.src e)).1,v) = atSite (N.dst e) := p
  have group := congrArg (fun z : J × V => z.1) lifted
  have vertex := congrArg (fun z : J × V => z.2) lifted
  have raw : ((atSite (N.src e)).1,old (N.src e))=((atSite (N.dst e)).1,old (N.dst e)) :=
    Prod.ext group (same e)
  have dst := congrArg layout raw
  have nextGroup := congrArg (fun z : E × Block m => z.1) dst
  exact ⟨congrArg (fun z : E × Block m => z.2) dst,
    Finset.mem_map.mpr ⟨v,close,Prod.ext nextGroup vertex⟩⟩

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
