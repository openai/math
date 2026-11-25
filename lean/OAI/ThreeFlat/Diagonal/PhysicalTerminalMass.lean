import OAI.ThreeFlat.Diagonal.PhysicalArchiveRows
import OAI.ThreeFlat.Diagonal.PhysicalRecordFamily
import OAI.ThreeFlat.Diagonal.PhysicalRunCharges

namespace OAI
/-! # Inherited endpoint pairs and terminal incident width in a native root charge -/

namespace ThreeFlat.Diagonal.PhysicalStage
open scoped Classical BigOperators
open HistoryContraction
noncomputable section
variable {F : Type} [Field F]

namespace Run

theorem rawLayerSite {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) :
    r.readTerminal (fun X => X.Site) h = (r.terminalLayer h).state.Site :=
  terminal_relation (fun X => X.Site) (fun {d l} X => (⟨d,l,X⟩ : WireLayer))
    (fun X s => X=s.state.Site) (fun _ => rfl) r h

private def rawIncident {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (v : r.readTerminal (fun X => X.Site) h) :=
  (r.terminalLayer h).state.incidentWidth (cast (r.rawLayerSite h) v)

/-- Incidences of the actual terminal state on the chosen final tensor site. -/
def terminalIncident {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (v : (r.plan.finish h).Site) :=
  (r.terminalLayer h).state.incidentWidth (cast (congrArg Shape.Site (r.terminalLayer_shape h)).symm v)

private theorem incident_cast {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (v : (r.plan.finish h).Site) : r.rawIncident h ((r.finalSite h).symm v) = r.terminalIncident h v := by
  apply congrArg (r.terminalLayer h).state.incidentWidth
  have H {X Y : Type} (e : X=Y) (y : Y) : HEq ((Equiv.cast e).symm y) y := by cases e; rfl
  exact eq_of_heq (((cast_heq (r.rawLayerSite h) _).trans (H _ v)).trans (cast_heq _ v).symm)

private theorem rawCoverage {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (floor : r.LocalFloor C) (start pay : A.Site→ℕ)
    (hs : ∀ a, 1+A.incidentWidth a+pay a ≤ start a) (v : r.readTerminal (fun X => X.Site) h) :
    1+r.rawIncident h v+fiberMass (r.rawDestination h) pay v ≤ r.rootArray h C start v := by
  induction r with
  | done A =>
    change 1+A.incidentWidth v+fiberMass id pay v ≤ start v
    exact (congrArg (fun z : ℕ => 1+A.incidentWidth v+z) (fiberMass_id pay v)).trans_le (hs v)
  | step R next ih =>
    let t := h.1
    let rest := tailHistory R next h
    have children (j : (R.next t).Site) :
        1+(R.next t).incidentWidth j+fiberMass (R.parent t) pay j ≤ R.push t (C.1 t) start j := by
      apply Nat.add_le_add ((floor t).1 j)
      apply Finset.sum_le_sum
      intro i hi
      have := hs i.val
      omega
    change 1+(next t).rawIncident rest v+
      fiberMass ((next t).rawDestination rest ∘ R.parent t) pay v ≤ _
    have mass := fiberMass_comp (R.parent t) ((next t).rawDestination rest) pay v
    exact (congrArg (fun z : ℕ => 1+(next t).rawIncident rest v+z) mass).trans_le
      (ih t rest (C.2 t) (floor t).2 (R.push t (C.1 t) start) (fiberMass (R.parent t) pay) children v)

end Run

theorem Block.terminal_charge_covers (B : Block F) (n rem : ℕ)
    (A : State (2^B.exponent 0) ((B.repeat n).charge+rem)) (h : ((B.repeat n).run rem A).plan.History)
    (start payload : A.Site → ℕ) (hs : ∀ a,1+A.incidentWidth a+payload a≤ start a)
    (v : (((B.repeat n).run rem A).plan.finish h).Site) :
    let r := (B.repeat n).run rem A
    1+r.terminalIncident h v+(∑ a : {x // r.plan.destination h x=v},payload a.val) ≤
      r.chargeAt h (B.charges n rem A) start v := by
  let r := (B.repeat n).run rem A
  let e := r.finalSite h
  let iso : {a // r.plan.destination h a=v} ≃ {a // r.rawDestination h a=e.symm v} :=
    Equiv.subtypeEquivRight fun a => by
      rw [←r.finalSite_rawDestination h a]
      change e _ = v ↔ _
      constructor
      · intro H
        simpa only [Equiv.symm_apply_apply] using congrArg e.symm H
      · intro H
        rw [H,Equiv.apply_symm_apply]
  have mass : (∑ a : {x // r.plan.destination h x=v},payload a.val) =
        fiberMass (r.rawDestination h) payload (e.symm v) :=
    iso.sum_comp (fun a=>payload a.val)
  change 1+r.terminalIncident h v + (∑ a : {x // r.plan.destination h x=v},payload a.val) ≤
    r.chargeAt h (B.charges n rem A) start v
  rw [mass, ←r.incident_cast h v]
  exact r.rawCoverage h _ ((B.repeat n).certified_floor _ (B.factor_bound n) rem A) start payload hs _

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
