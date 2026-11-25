import OAI.Hierarchy.DescentDatedCableJobCatalog

namespace OAI
/-! An original cable operand selects the same old source, old target or redirected pair
in the physical packet matcher and in the literal expanded gadget boundary. -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentKernelHistory
open DescentCableDonorNames DescentBundleHistory GadgetNetwork
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k : ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε J V k) (he:0≤ε) (c:(A.stage.result he).Choice)
local notation "r" => BitDescription.scannedRows he A.stage
local notation "N" => W.graph
local notation "M" => rawGraph he A.stage c
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "supply" => branchWidth G (fun _:(r).pairs=>A.stage.z) ((r).profile c)
local notation "posn" => DescentSharedCableNames.Stage.Positive A
local notation:max "row" e:max => (⟨DescentCableDonorNames.anchor (r).pick (e:DescentRawCablePanel.Live A (r).pick).val,(e).property⟩:posn)
local notation "T" => nativeTraffic N W.core home
local notation:max "member" ci:max m:max side:max => (⟨(picked A he ci m side).val,
  A.quantum_positive _ (picked A he ci m side).property.1⟩:posn)

def projectedWire {d:ℕ} {bits:P→ℕ} (graph:Network d P bits) (v:graph.Site) : Boundary graph v→Option graph.Edge :=
  Sum.elim (fun t=>some t.val) (fun _=>none)

open private Hierarchy.DescentKernelHistory.oldTarget from OAI.Hierarchy.DescentGadgetHistory in
theorem exact_old_port (v:(N).Site) (leg:Incident N v) (positive:0<A.grainCount leg.val)
    (e:DescentRawCablePanel.Live A (r).pick)
    (observed:projectedWire M (.inl v) (oldBoundary N (r).pick supply v (.inl leg))=some e.val) :
    CablePort A he (⟨leg.val,positive⟩:posn) (if (N).src leg.val=v then 0 else 1) (row e) (role e.val) :=by
  classical
  let prior:posn:=⟨leg.val,positive⟩
  by_cases src:(N).src leg.val=v
  · have got := observed
    rw [oldBoundary,dite_eq_left src] at got
    have retr : e.val=.inl leg.val := (Option.some.inj got).symm
    rcases e with ⟨raw,h⟩
    dsimp only at retr
    subst raw
    simpa only [ite_eq_left src,DescentCableDonorNames.anchor,role] using CablePort.source (A:=A) (he:=he) prior
  · let dst := leg.property.resolve_left src
    let actual : Option ((r).pairs×Fin 2) → (M).Edge
      | none => .inl leg.val
      | some t => .inr (.inl t)
    have decode (o : Option ((r).pairs×Fin 2)) (found : GadgetNetwork.selected N (r).pick leg.val=o) :
        projectedWire M (.inl v) (Hierarchy.DescentKernelHistory.oldTarget N (r).pick supply v
          leg.val dst o found) = some (actual o) := by
      cases o <;> rfl
    have got := observed
    rw [oldBoundary,dite_eq_right src,decode] at got
    have resolved : e.val=actual (GadgetNetwork.selected N (r).pick leg.val) := (Option.some.inj got).symm
    cases chosen:GadgetNetwork.selected N (r).pick leg.val with
    | none=>
      have retr:e.val=.inl leg.val:=by simpa only [chosen,actual] using resolved
      have miss:∀(m:Matched T A.cap (thinList home color (home ((N).src leg.val)))
          (thickList home color (home ((N).src leg.val)))) (side:Bool),
          (picked A he (home ((N).src leg.val)) m side).val≠leg.val:=by
        intro m side eqn
        let t:(r).pairs×Fin 2:=(⟨home ((N).src leg.val),m⟩,if side then 0 else 1)
        have old:(r).pick t=leg.val:=(picked_old A he _ m side).symm.trans eqn
        have yes:GadgetNetwork.selected N (r).pick leg.val=some t:=old ▸ GadgetNetwork.selected_pick N (r).pick t
        rw [chosen] at yes
        contradiction
      rcases e with ⟨raw,h⟩
      dsimp only at retr
      subst raw
      simpa only [ite_eq_right src,DescentCableDonorNames.anchor,role] using CablePort.kept (A:=A) (he:=he) prior miss
    | some t=>
      have old:(r).pick t=leg.val:=GadgetNetwork.selected_spec N (r).pick chosen
      have retr:e.val=.inr (.inl t):=by simpa only [chosen,actual] using resolved
      rcases e with ⟨raw,h⟩
      dsimp only at retr
      subst raw
      rcases t with ⟨⟨ci,m⟩,side⟩
      have first:(member ci m true).val=(r).pick (⟨ci,m⟩,0):=picked_old A he ci m true
      fin_cases side
      · have initial:(member ci m true)=prior:=Subtype.ext (first.trans old)
        have parent:(member ci m true)=(⟨(r).pick (⟨ci,m⟩,0),h⟩:posn):=Subtype.ext first
        have out:=CablePort.redirected (A:=A) (he:=he) ci m true
        rw [ite_eq_right src]
        change CablePort A he prior 1 (⟨(r).pick (⟨ci,m⟩,0),h⟩:posn) 1
        rw [←initial,←parent]
        exact out
      · have initial:(member ci m false)=prior:=Subtype.ext ((picked_old A he ci m false).trans old)
        have parent:(member ci m true)=(⟨(r).pick (⟨ci,m⟩,0),h⟩:posn):=Subtype.ext first
        have out:=CablePort.redirected (A:=A) (he:=he) ci m false
        rw [ite_eq_right src]
        change CablePort A he prior 1 (⟨(r).pick (⟨ci,m⟩,0),h⟩:posn) 2
        rw [←initial,←parent]
        exact out

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
