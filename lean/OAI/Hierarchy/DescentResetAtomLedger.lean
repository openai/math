import OAI.Hierarchy.DescentTrunkReadout
import OAI.Hierarchy.DescentStageAtoms

namespace OAI
/-! # Keeping every old record once in the grouped reset and recording the installed router tables -/

namespace Hierarchy.DescentResetTrunks
open DescentSixParty Computability.BorderVNP.Crossing DescentResetAttachments
open scoped Classical BigOperators
noncomputable section
variable {F P H Q : Type} [Field F] [Fintype H] [Fintype Q] {n d : ℕ} {bits : P→ℕ}
variable (A : MarkedWorld F n P bits) (home : A.graph.Site→H) (group : Bool→A.graph.Edge→Q) (hub : H→Bool)
variable {w : A.graph.Edge→ℕ} (same : w=A.graph.width) (R : Network d (Bool×Q) (DescentRouterBank.publicWidth group w)) (tab : R.Tables F)

/-- Physical terminal/relay/hardware tags of the installed graph, including the width cast. -/
def installedNames : (install A home group hub same R tab).graph.Site ≃ ((Bool×H)⊕R.Site) := by
  subst w
  exact Equiv.refl _

end
end Hierarchy.DescentResetTrunks

namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks StarKeys
open scoped Classical BigOperators
noncomputable section
variable {F P Old : Type} [Field F] {n : ℕ} {bits : P→ℕ} {W : MarkedWorld F n P bits} {price ε : ℝ} {h C Ht : ℕ}
variable (Z : ResetInput W price ε h C Ht) (T : Terminals Z)
local notation "post" => reenter Z T

def resetNames : (post).graph.Site ≃ ((Bool×Z.Fallback)⊕Z.bank.Site) :=
  installedNames W T.home Z.placement.input T.hub (funext fun e => (Z.allWidths e).symm) Z.bank Z.tables

def oldOwner (u : W.graph.Site) : (post).graph.Site := (resetNames Z T).symm (.inl (false,T.home u))
def tableOwner (v : Z.bank.Site) : (post).graph.Site := (resetNames Z T).symm (.inr v)

/-- Each configured router site supplies its one actual table descriptor. Extra terminal
pin/identity descriptors, if stored individually, have an explicitly indexed fresh list. -/
def reentryRecords {Pin : Type} (rec : W.graph.Site→List Old) (extra : (post).graph.Site→List Pin)
    (v : (post).graph.Site) : List (Old ⊕ (Z.bank.Site ⊕ Pin)) :=
  gather (fun u : {u : W.graph.Site // oldOwner Z T u=v}=> (rec u.val).map Sum.inl) ++
    gather (fun t : {r : Z.bank.Site // tableOwner Z T r=v}=>[Sum.inr (Sum.inl t.val)]) ++
    (extra v).map (Sum.inr ∘ Sum.inr)

/-- Equality in the retained history count, with no copying cost for old tables whose
incident cables split into several parallel pieces or attach to different hardware. -/
theorem reentryRecords_count {Pin : Type} (rec : W.graph.Site→List Old) (extra : (post).graph.Site→List Pin) :
    (∑v : (post).graph.Site,(reentryRecords Z T rec extra v).length)=
      (∑u,(rec u).length)+Fintype.card Z.bank.Site+(∑v,(extra v).length) := by
  classical
  have fiber {U : Type} [Fintype U] (loc : U→(post).graph.Site) (weight : U→ℕ) :
      (∑v,∑u : {u // loc u=v},weight u.val)=∑u,weight u := by
    rw [←Fintype.sum_sigma' (fun v (u : {u //loc u=v})=>weight u.val)]
    exact (Equiv.sigmaFiberEquiv loc).sum_comp weight
  simp only [reentryRecords,List.length_append,gather_length,List.length_map,List.length_singleton,
    Finset.sum_add_distrib]
  rw [fiber (oldOwner Z T) (fun u=>(rec u).length),fiber (tableOwner Z T) (fun _=>1)]
  simp

theorem tableOwner_injective : Function.Injective (tableOwner Z T) := by
  intro x y h
  exact Sum.inr.inj ((resetNames Z T).symm.injective h)

/-- One configured table is recorded at each real bank site. Grid contacts and terminal
slots receive new pins only when the explicit descriptor list asks for them. -/
theorem reentry_birth_limit {Pin : Type} (extra : (post).graph.Site→List Pin) (v : (post).graph.Site) :
    (reentryRecords Z T (fun _=>([] : List Empty)) extra v).length≤1+(extra v).length := by
  classical
  let Gate := {r : Z.bank.Site // tableOwner Z T r=v}
  let : Subsingleton Gate := ⟨fun x y=>Subtype.ext (tableOwner_injective Z T (x.property.trans y.property.symm))⟩
  have bound : Fintype.card Gate≤1 := Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  simpa [reentryRecords,gather_length,Gate] using Nat.add_le_add_right bound (extra v).length

theorem reentry_birth_total {Pin : Type} (extra : (post).graph.Site→List Pin) :
    (∑v,(reentryRecords Z T (fun _=>([] : List Empty)) extra v).length)=
      Fintype.card Z.bank.Site+∑v,(extra v).length := by
  simpa using reentryRecords_count Z T (fun _=>([] : List Empty)) extra

private theorem fiber_count {U : Type} [Fintype U] (atKey : U→(post).graph.Site)
    (v : (post).graph.Site) (cost : U→ℕ) : (∑u : {u // atKey u=v},cost u.val)=
      ∑u,if atKey u=v then cost u else 0 := by
  rw [←Finset.sum_subtype (Finset.univ.filter (fun u=>atKey u=v)) (by simp) cost,Finset.sum_filter]

private theorem physical_length {Pin : Type} (rec : W.graph.Site→List Old)
    (name : (Bool×Z.Fallback)⊕Z.bank.Site) :
    (reentryRecords Z T rec (fun _=>([] : List Pin)) ((resetNames Z T).symm name)).length =
      (∑u, if Sum.inl (false,T.home u)=name then (rec u).length else 0)+
      (∑r : Z.bank.Site,if Sum.inr r=name then 1 else 0) := by
  simp only [reentryRecords,List.length_append,List.length_map,List.length_nil,List.length_singleton,
    gather_length,add_zero]
  rw [fiber_count Z T (oldOwner Z T) _ (fun u=>(rec u).length),
    fiber_count Z T (tableOwner Z T) _ (fun _=>1)]
  simp only [oldOwner,tableOwner,Equiv.apply_eq_iff_eq]

/-- An original primary terminal gathers precisely the old sites at its indicated row. -/
theorem reentry_primary_length {Pin : Type} (rec : W.graph.Site→List Old) (t : Z.Fallback) :
    (reentryRecords Z T rec (fun _=>([] : List Pin)) ((resetNames Z T).symm (.inl (false,t)))).length =
      ∑u : {u : W.graph.Site // T.home u=t},(rec u.val).length := by
  rw [physical_length,←Finset.sum_subtype (Finset.univ.filter (fun u=>T.home u=t)) (by simp) (fun u=>(rec u).length),
    Finset.sum_filter]
  simp

/-- The other terminal phase is a pure relay and stores no old list or configured bank gate. -/
theorem reentry_relay_length {Pin : Type} (rec : W.graph.Site→List Old) (t : Z.Fallback) :
    (reentryRecords Z T rec (fun _=>([] : List Pin)) ((resetNames Z T).symm (.inl (true,t)))).length=0 := by
  rw [physical_length];simp

/-- Each actual bank site stores its own configured table descriptor. -/
theorem reentry_bank_length {Pin : Type} (rec : W.graph.Site→List Old) (r : Z.bank.Site) :
    (reentryRecords Z T rec (fun _=>([] : List Pin)) ((resetNames Z T).symm (.inr r))).length=1 := by
  rw [physical_length];simp

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
