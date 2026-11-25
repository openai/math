import OAI.Hierarchy.TaggedWideReadoutParts
import OAI.Hierarchy.TaggedWidePhysical

namespace OAI
/-! # A cofinal protocol readout from the actual priced guarded circuits -/
noncomputable section
namespace Hierarchy.Tagged
open Filter Real Set TaggedShorterBudget TaggedPrune WideControlJoin
open scoped Classical BigOperators Topology
variable {F : Type*} [Field F] {k M n N : ℕ} {κ A δ ξ : ℝ} {u : ℝ→ℝ}
variable (geom : DyadicGeometry κ A n)
local notation "Menu" => geom.menu u δ ξ

/-- The code-size and small native clock estimates remain explicit. The
semantic input at each parent consists of the original machines, fixed site
gates, actual cut compactors and their individual charged terms. -/
theorem protocolReadout_of_native (hM : 0<M)
    (eligible : WideParent κ A→Prop) (large : ∀ᶠ x in WideParent.large κ A,eligible x)
    (parts : ∀x,eligible x→Parts F k x.h x.w M n)
    (execution : ∀x (v:eligible x),(parts x v).Run)
    («prefix» : ∀x (v:eligible x),let a:=parts x v
      a.first.m=controlHeight x.h (a.first.S+(a.first.f+a.first.u)))
    (paid : ∀x (v:eligible x),let a:=parts x v
      a.paid.m=controlHeight x.h (a.paid.S+(a.paid.f+a.paid.u)))
    (slots : ∀x (v:eligible x),let a:=parts x v
      a.paid.S+(a.paid.f+a.paid.u)≤2^a.paid.m)
    (cuts : ∀x (v:eligible x) i,let a:=parts x v
      (a.cut i).bank (a.cap i)=(Menu).bank x i)
    (cpu : ∀ᶠ x in WideParent.large κ A,∀v:eligible x,∀b,
      (parts x v).charges.cpu b≤20000000*2^(controlHeight x.h ((parts x v).charges.rows b))*(x.h+1)*(N+1)^2)
    (fees : ∀i:WidePhysicalBill.Part n,∃C d:ℝ,0≤C ∧ 0≤d ∧
      ∀ᶠ x in WideParent.large κ A,∀v:eligible x,
        WidePhysicalBill.Part.fee (parts x v).charges i≤C*(WidePhysicalBill.Part.scale x.h x.w i*(log (x.h:ℝ))^d)) :
    Nonempty (ProtocolReadout F k u κ A δ ξ) := by
  let vacant : WidePhysicalBill.Charges n:=⟨fun _=>0,fun _=>0,0,0,fun _=>0,fun _=>0,0,0,0⟩
  let c (x:WideParent κ A) := if v:eligible x then (parts x v).charges else vacant
  have bill : ∀i:WidePhysicalBill.Part n,∃C d:ℝ,0≤C ∧ 0≤d ∧
      ∀ᶠ x in WideParent.large κ A,
        WidePhysicalBill.Part.fee (c x) i≤C*(WidePhysicalBill.Part.scale x.h x.w i*(log (x.h:ℝ))^d) := by
    intro i
    obtain ⟨C,d,hC,hd,ev⟩:=fees i
    refine ⟨C,d,hC,hd,?_⟩
    filter_upwards [large,ev] with x v bound
    simpa only [c,dite_eq_left v] using bound v
  have hw : ∀ᶠ x in WideParent.large κ A,∀b,(c x).cpu b≤
      20000000*2^(controlHeight x.h ((c x).rows b))*(x.h+1)*(N+1)^2 := by
    filter_upwards [large,cpu] with x v small
    simpa only [c,dite_eq_left v] using small v
  obtain ⟨C,d,hC,hd,ev⟩:=WidePhysicalBill.of_component_bounds c hw bill
  let counts (x:WideParent κ A):=WideHost.dualControlRows x.h ((c x).rows false) ((c x).rows true)
  refine ⟨⟨n,57,M,hM,geom,C,d,hC,hd,counts,ev.mono (fun _ p=>p.1),?_⟩⟩
  filter_upwards [large,ev] with x v price
  dsimp only
  let a:=parts x v
  have eq:(fun i=>(a.cut i).bank (a.cap i))=(Menu).bank x:=funext (cuts x v)
  have charge:c x=a.charges:=dite_eq_left v
  obtain ⟨b,cost,sel⟩:=a.built (execution x v) («prefix» x v) (paid x v) (slots x v)
  have bounds:=price.2 b.cost b.selectors (charge.symm ▸ cost) (charge.symm ▸ sel)
  have shape:(fun j=>controlHeight x.h (counts x j))=
      (fun j=>controlHeight x.h (WideHost.dualControlRows x.h (a.charges.rows false) (a.charges.rows true) j)) := by
    simp only [counts,charge]
  rw [←eq,shape]
  exact ⟨b,bounds⟩

end Hierarchy.Tagged

end
end OAI
