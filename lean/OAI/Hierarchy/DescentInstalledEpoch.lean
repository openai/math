import OAI.Hierarchy.DescentResetUniform
import OAI.Hierarchy.DescentResetChosenBill
import OAI.Hierarchy.DescentMeasuredEpoch

namespace OAI
/-! # The measured epoch closes on the true dyadic rotor and fallback circuits -/

namespace Hierarchy.DescentSixParty
open DescentGL DescentColonies DescentBaseVariance DescentChosenRouter DescentMixedRouter
open DescentResetInvoice DescentContactTree DescentResetAttachments Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F] {d : ℕ} {P : Type} {bits : P→ℕ}

/-- Quantities read from the chosen reset placement on this branch. All pool,
hardware, naming and routing fields describe real input devices. -/
structure ResetInput (A : MarkedWorld F d P bits) (price ε : ℝ) (h C Ht : ℕ) where
  V : Type
  [finiteV : Fintype V]
  [decideV : DecidableEq V]
  Fallback : Type
  [finiteF : Fintype Fallback]
  Contact : Type
  [finiteC : Fintype Contact]
  k : ℕ
  n : ℕ
  width : ℕ
  unit : ℕ
  allWidths : ∀e,A.graph.width e=unit
  hub : A.graph.Site→Bool
  inside : ∀e∈A.core,hub (A.graph.src e)=false ∧ hub (A.graph.dst e)=false
  outside : ∀e∉A.core,hub (A.graph.src e)≠hub (A.graph.dst e)
  placement : Placement V A.graph.Edge Fallback Contact k (2^n)
  graph : NonlinearExpanders.Graph n h
  positive : 0<width
  pay : ℝ
  scale : ℝ
  hn : 0≤pay
  rate : price*pay=scale
  circuit : Hardware (K:=F) (C₀:=C) (u:=unit) placement graph positive pay
  hops : ℕ
  weight : V→Block k→ℝ
  ordinary : ∀i∈A.core,∀s,¬placement.hub (placement.old s i).1
  incidences : ∀p,load (placement.old false) (fun i=>if i∈A.core then price*unit else 0) p +
      load (placement.old true) (fun i=>if i∈A.core then price*unit else 0) p ≤ weight p.1 p.2
  fallback : ∀i∈badCore (selected placement graph positive pay circuit) A.core,
      edgeHops (selected placement graph positive pay circuit) i≤hops
  exterior : ∀i∉A.core,edgeHops (selected placement graph positive pay circuit) i≤Ht
  loadBill : (∑v,∑i,weight v i) ≤ 2*(price*A.liveWidth)+257*(price*A.tetherWidth)+ε
  span : scale*(∑v,(2:ℝ)^placement.b v) ≤ 4*(ε+∑v,∑i,weight v i)
  marked : (hops:ℝ)*(∑p∈validBases placement.b placement.keys,baseValue placement.b
    placement.depth weight placement.L p) ≤ ε+∑v,∑i,weight v i

attribute [instance] ResetInput.finiteV ResetInput.decideV ResetInput.finiteF ResetInput.finiteC

namespace ResetInput
variable {A : MarkedWorld F d P bits} {price ε : ℝ} {h C Ht : ℕ}
variable (Z : ResetInput A price ε h C Ht) (hp : 0≤price) (he : 0≤ε)

def bank (Z : ResetInput A price ε h C Ht) :=
  let R := Z.placement
  DescentMixedRouter.network (K:=F) (C₀:=C) Z.graph Z.positive Z.unit R.contact R.input R.site R.owner R.align
    (selected R Z.graph Z.positive Z.pay Z.circuit) d

def tables (Z : ResetInput A price ε h C Ht) : Z.bank.Tables F :=
  let R := Z.placement
  DescentMixedRouter.coefficients (K:=F) (C₀:=C) Z.graph Z.positive Z.unit R.contact R.input R.site R.owner R.align
    (selected R Z.graph Z.positive Z.pay Z.circuit) d

def world (Z : ResetInput A price ε h C Ht) (_hp : 0≤price) (_he : 0≤ε) :=
  DescentResetAttachments.mount A Z.hub Z.placement.input (funext fun e=>(Z.allWidths e).symm) Z.bank Z.tables

def hubAfter (Z : ResetInput A price ε h C Ht) :=
  DescentResetAttachments.mountHub A Z.hub Z.placement.input (funext fun e=>(Z.allWidths e).symm) Z.bank Z.tables

theorem installed :
    let W := Z.world hp he
    let newHub := Z.hubAfter
    (∀x,W.value x=A.value x) ∧ W.tetherWidth=A.tetherWidth ∧
      (∀e∈W.core,newHub (W.graph.src e)=false ∧ newHub (W.graph.dst e)=false) ∧
      (∀e∉W.core,newHub (W.graph.src e)≠newHub (W.graph.dst e)) ∧
      price*W.liveWidth≤ splicedRate h C*(price*A.liveWidth+ε)+
        splicedExteriorRate h C 256 Ht*(price*A.tetherWidth) := by
  let R := Z.placement
  let sel := selected R Z.graph Z.positive Z.pay Z.circuit
  let bank := DescentMixedRouter.network (K:=F) (C₀:=C) Z.graph Z.positive Z.unit R.contact R.input R.site R.owner R.align sel d
  let tables := DescentMixedRouter.coefficients (K:=F) (C₀:=C) Z.graph Z.positive Z.unit R.contact R.input R.site R.owner R.align sel d
  have core : (A.liveWidth:ℝ)=∑_i∈A.core,(Z.unit:ℝ) := by
    simp only [MarkedWorld.liveWidth,Nat.cast_sum,Z.allWidths]
  have tether : (A.tetherWidth:ℝ)=∑_i∈A.coreᶜ,(Z.unit:ℝ) := by
    simp only [MarkedWorld.tetherWidth,Nat.cast_sum,Z.allWidths]
  refine DescentResetAttachments.install A Z.hub R.input (d:=d) (funext fun e=>(Z.allWidths e).symm)
    bank tables (DescentMixedRouter.value (K:=F) (C₀:=C) Z.graph Z.positive Z.unit R.contact R.input R.site R.owner R.align sel)
    Z.inside Z.outside price ε hp he h C 256 Ht ?_
  rw [core,tether]
  exact chosen_invoice R Z.graph Z.positive Z.circuit d A.core Z.hops Ht Z.weight
    hp Z.hn he (by norm_num) Z.rate Z.ordinary Z.incidences Z.fallback Z.exterior
    (by simpa only [←core,←tether,show ((256 : ℕ) : ℝ)+1=257 by norm_num] using Z.loadBill) Z.span Z.marked

theorem value (x : Ports bits) : (Z.world hp he).value x=A.value x :=
  (installed Z hp he).1 x

theorem tether : (Z.world hp he).tetherWidth=A.tetherWidth :=
  (installed Z hp he).2.1

theorem bill : price*(Z.world hp he).liveWidth≤ splicedRate h C*(price*A.liveWidth+ε)+
    splicedExteriorRate h C 256 Ht*(price*A.tetherWidth) :=
  (installed Z hp he).2.2.2.2

end ResetInput
end
end Hierarchy.DescentSixParty

end OAI
