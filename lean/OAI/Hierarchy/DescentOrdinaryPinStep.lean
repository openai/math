import OAI.Hierarchy.DescentOrdinaryPinGeometry
import OAI.Hierarchy.DescentIssuedChronology

namespace OAI
/-! # Binary coordinates of the genuine ordinary subround on original pins -/

namespace Hierarchy.DescentSixParty.Chronology
open Computability.BorderVNP.Crossing Catalyst DescentCompiler DescentGL DescentColonies DescentExterior DescentKernelHistory
open PinCohorts
noncomputable section

variable {F P : Type} [Field F] [Fintype P] {d k tail : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {q ε u : ℝ} {S : AtomSchedule}
  {W : MarkedWorld F d P bits} {i z D wire hist z' D' : ℕ}

omit [Fintype P] in
theorem OrdinaryLink.previous_host_of_equal {source : Reached W G q ε S k i z D wire hist} {he : 0≤ε}
    {T : StageInput W G u ε} {p : (T.result he).Choice} {n : Normalize ((T.result he).state p)}
    {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink source he T p n target)
    (owns : ∀pin,source.placement.hub (host source pin)=true) {a b : P}
    (eqn : host target a=host target b) : host source a=host source b := by
  classical
  obtain ⟨_age,_radix,chart,rows⟩:=ticket.hubRows
  have before:=congrArg Prod.fst ((rows a (owns a)).2.symm.trans
    ((congrArg chart eqn).trans (rows b (owns b)).2))
  exact before

def OrdinaryLink.pinStep {source : Reached W G q ε S k i z D wire hist} {he : 0≤ε}
    {T : StageInput W G u ε} {p : (T.result he).Choice} {n : Normalize ((T.result he).state p)}
    {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink source he T p n target) (base : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (owns : ∀pin,source.placement.hub (host source pin)=true) :
    Step source target base radix := by
  classical
  let age:=ticket.hubRows.choose
  let second:=ticket.hubRows.choose_spec
  let chart:=second.choose_spec.choose
  have rows:=second.choose_spec.choose_spec
  let L:=multiplier source.placement.fieldBits (BitDescription.scannedRows he source.placement.stage).μ
  let gain:=DescentHostDegree.gainExponent 20 source.placement.degree
  exact ordinaryGeometry base radix age L chart
    (fun v block=>(v,(k-gain,group (k-gain) (rearrange L block)),0))
    (fun pin=>(rows pin (owns pin)).1) (fun pin=>(rows pin (owns pin)).2)

end
end Hierarchy.DescentSixParty.Chronology

end OAI
