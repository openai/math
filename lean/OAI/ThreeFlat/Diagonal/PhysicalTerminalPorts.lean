import OAI.ThreeFlat.Diagonal.PhysicalTerminalMass
import OAI.ThreeFlat.Diagonal.PhysicalWordAssembly

namespace OAI
/-! # Port widths of the terminal word layout of a physical program -/

namespace ThreeFlat.Diagonal.PhysicalStage
open scoped Classical BigOperators
open HistoryContraction
noncomputable section
variable {F Pins : Type} [Field F] {d l D m : ℕ} {A : State d l}

private theorem Run.raw_ext_fiber (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (v : r.readTerminal (fun X => X.Site) h) :
    (r.endWords h J L).ext (cast (r.rawLayerSite h) v)=fiberMass (r.rawDestination h) L.ext v := by
  induction r with
  | done A=>exact (fiberMass_id L.ext v).symm
  | step R next ih=>
    let t:=h.1
    let rest:=tailHistory R next h
    let s:=J.1 L t
    change ((next t).endWords rest (J.2 t) s.words).ext (cast ((next t).rawLayerSite rest) v)=
      fiberMass ((next t).rawDestination rest ∘ R.parent t) L.ext v
    have layers : s.words.ext=fiberMass (R.parent t) L.ext := funext s.ext_fiber
    exact (ih t rest (J.2 t) s.words v).trans
      ((congrArg (fun pay => fiberMass ((next t).rawDestination rest) pay v) layers).trans
        (fiberMass_comp (R.parent t) ((next t).rawDestination rest) L.ext v).symm)


/-- The actual terminal view contains precisely the original external words whose
source sites contract onto this final tensor site. -/
theorem Run.terminal_ext_sum (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (site : (r.plan.finish h).Site) :
    let z:=cast (congrArg Shape.Site (r.terminalLayer_shape h)).symm site
    (r.endWords h J L).ext z=∑ a : {x // r.plan.destination h x=site},L.ext a.val := by
  let e:=r.finalSite h
  let iso : {a // r.plan.destination h a=site} ≃ {a // r.rawDestination h a=e.symm site} :=
    Equiv.subtypeEquivRight fun a=>by
      rw [←r.finalSite_rawDestination h a]
      change e _=site ↔ _
      constructor
      · intro H
        simpa only [Equiv.symm_apply_apply] using congrArg e.symm H
      · intro H
        rw [H,Equiv.apply_symm_apply]
  have H {X Y : Type} (eqn : X=Y) (v : Y) : HEq ((Equiv.cast eqn).symm v) v := by cases eqn;rfl
  have same : cast (r.rawLayerSite h) (e.symm site)=cast (congrArg Shape.Site (r.terminalLayer_shape h)).symm site :=
    eq_of_heq (((cast_heq _ _).trans (H _ site)).trans (cast_heq _ _).symm)
  exact (congrArg (r.endWords h J L).ext same.symm).trans
    ((r.raw_ext_fiber h J L (e.symm site)).trans ((iso.sum_comp (fun a=>L.ext a.val)).symm))

private theorem assembled_width_cast {X Y : Shape} (eqn : X=Y) {V : Form X Pins} {U : Form Y Pins}
    (h : HEq V U) (z : X.Site) : V.width z=U.width (cast (congrArg Shape.Site eqn) z) := by
  cases eqn
  cases eq_of_heq h
  rfl

/-- Exact compiled arity at a chosen terminal root, including the true external
word prefix and all native incidence sectors. -/
theorem Run.terminal_width_exact (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (ordered : A.OrderedHalves L) (N : Forest F L.ports.form) (v : (r.plan.finish h).Site) :
    let z:=cast (congrArg Shape.Site (r.terminalLayer_shape h)).symm v
    (r.plan.assemble h (r.wordAssembly J L) N).1.width v=(r.endWords h J L).ext z+r.terminalIncident h v := by
  let z:=cast (congrArg Shape.Site (r.terminalLayer_shape h)).symm v
  have result:=assembled_width_cast (r.terminalLayer_shape h).symm (r.endWords_form h J L N) v
  exact result.trans (congrArg (fun n=>(r.endWords h J L).ext z+n)
    ((r.endWords_halves h J L ordered).halfBits_eq_incident z))

end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.PhysicalStage
open HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F Pins : Type} [Field F] {d l : ℕ} {A : State d l}

private theorem Run.raw_width_bound (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r) (L : A.Words Pins)
    (C : r.Charges) (floor : r.LocalFloor C) (start : A.Site→ℕ) (width : ∀ x,L.ports.form.width x≤2*start x)
    (w : r.readTerminal (fun X=>X.Site) h) :
    (r.endWords h J L).ports.form.width (cast (r.rawLayerSite h) w)≤2*r.rootArray h C start w := by
  induction r with
  | done A=>exact width w
  | step R next ih=>
    let s:=J.1 L h.1
    exact ih h.1 (tailHistory R next h) (J.2 h.1) s.words (C.2 h.1) (floor h.1).2 (R.push h.1 (C.1 h.1) start)
      (s.width_push start (C.1 h.1) width (floor h.1).1) w

/-- Twice the unscaled S43 charge covers the entire terminal pin namespace. -/
theorem Run.assembled_width (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r) (L : A.Words Pins)
    (N : Forest F L.ports.form) (C : r.Charges) (floor : r.LocalFloor C) (start : A.Site→ℕ)
    (width : ∀ x,L.ports.form.width x≤2*start x) (v : (r.plan.finish h).Site) :
    (r.plan.assemble h (r.wordAssembly J L) N).1.width v≤2*r.chargeAt h C start v := by
  let w:=(r.finalSite h).symm v
  have align {X Y : Type} (eqn : X=Y) (y : Y) : HEq ((Equiv.cast eqn).symm y) y :=by cases eqn;rfl
  have same : cast (r.rawLayerSite h) w=cast (congrArg Shape.Site (r.terminalLayer_shape h).symm) v :=
    eq_of_heq (((cast_heq _ _).trans (align _ v)).trans (cast_heq _ _).symm)
  rw [assembled_width_cast (r.terminalLayer_shape h).symm (r.endWords_form h J L N) v,←same]
  exact r.raw_width_bound h J L C floor start width w

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
