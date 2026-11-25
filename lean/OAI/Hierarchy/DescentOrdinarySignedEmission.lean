import OAI.Hierarchy.DescentOrdinaryWindowFields
import OAI.Hierarchy.DescentOrdinarySignedAll

namespace OAI
/-! The physical rank/panel apparatus is specialized to the named result of an actual ordinary rewrite. -/
namespace Hierarchy.DescentOrdinaryWindowFields
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.MarkedWorld DescentPhysicalOrder
open DescentHostDirectory DescentColonies DescentStageEdgeReceipt DescentPacking DescentCableDonorNames
open DescentSharedCableNames DescentSharedCableNames.Siblings DescentOrdinarySiblingSerial DescentParallelBase
open private DescentOrdinarySiblingSerial.physicalBase DescentOrdinarySiblingSerial.physicalKey
  from OAI.Hierarchy.DescentOrdinarySiblingSerial
open scoped Classical BigOperators
noncomputable section
variable {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
variable (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
local notation "sel" => W.selected G pick z hz fit pack p
variable (key : (W.selected G pick z hz fit pack p).graph.Site↪Key H) (flag : H→Bool) (k g q : ℕ)
variable (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
local notation "coarse" => coalesced sel key flag k g
local notation "world" => DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected
variable (site : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Site ↪ ℕ)
local notation "sparse" => DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site
local notation "next" => PhysicalRename.rankedWorld world site sparse
variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {stage : ℕ} {price ε : ℝ}
variable (A : GroupStage
    (PhysicalRename.rankedWorld
      (DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
      (DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site))
    G price ε J V stage)
set_option quotPrecheck false in
local notation "ord" => originalId (next).graph.Edge
local notation "stream'" => Stage.stream A ord
local notation "B" => Stage.source A ord

open DescentOrdinaryParentBlocks DescentNextSignedWindow DescentOrdinaryChildFields
variable {i : ℕ} (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (names : Stage.Host J V stage↪ℕ) (qp:0<q)
local notation "C₀" => blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp
/-- Every sorted child and the orientation of each endpoint come from the
ordinary graph's actual normalized edge, including positive unmarked tethers. -/
def signedEmission : DescentResetWindowFields.Emission A ord C₀ (fun e=>e∈(coarse).core) where
  units:=units W G edge pair pick z hz fit pack p key flag k g q old picked affected site A
  order_eq _ _:=rfl
  within_at e j := by
    have prior := within_at W G edge pair pick z hz fit pack p key flag k g q old picked affected site A e j
    by_cases hit : e ∈ (coarse).core <;> simp only [hit, ite_true, ite_false] at prior ⊢ <;> exact prior
  core_at:=core_at W G edge pair pick z hz fit pack p key flag k g q old picked affected site A
  first_of_edge e j := by
    have prior := first_of_edge W G edge pair pick z hz fit pack p key flag k g q old picked affected site A e j
    by_cases hit : e ∈ (coarse).core <;> simp only [DescentOrdinaryParentBlocks.firstGrain, hit, ite_true, ite_false] at prior ⊢ <;> exact prior

end
end Hierarchy.DescentOrdinaryWindowFields

end OAI
