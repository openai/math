import OAI.Hierarchy.DescentResetSourceTicketRAM
import OAI.Hierarchy.DescentResetSourceTicketStream
import OAI.Hierarchy.DescentResetWindowTicketCount

namespace OAI
/-! # A streamed short count reads the precise source-ticket shown by the raw prior tape -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open Computability.BorderVNP.Crossing DescentCompiler DescentColonies DescentPhysicalOrder DescentPacking
open DescentSharedCableNames DescentSharedCableNames.Siblings DescentParallelBase
open DescentStageEdgeReceipt DescentCableUnbundling
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "cnt" => fun e=>(coarse).graph.width e/(Z).unit
local notation "world" => (Z).orderedOrdinary T birth
local notation "tape" => (Z).nativeResetEdges T vertexCode birth
local notation "index" => (tape).order.trans Fin.valEmbedding
local notation "dense" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "groups" => S.groupCount (i+1)

open DescentResetSourceTicketRAM
def atRawSource (e f : (coarse).graph.Edge) : Prop :=
  Stage.home B.raw ((coarse).graph.src f)=Stage.home B.raw ((coarse).graph.src e) ∨
  Stage.home B.raw ((coarse).graph.dst f)=Stage.home B.raw ((coarse).graph.src e)

theorem sourceTicket_count_atRawSource (e : (coarse).graph.Edge) (he : 0 < weight B e) :
    (sourceTicket B e he).val = ∑ f, if atRawSource B e f ∧ (tape).rank f < (tape).rank e
      then (coarse).graph.width f / (Z).unit else 0 := by
  rw [sourceTicket_count]
  apply Finset.sum_congr rfl
  intro f _
  by_cases hit : atRawSource B e f ∧ (tape).rank f < (tape).rank e <;>
    simp only [atRawSource] at hit ⊢ <;> simp [hit]

variable {K b : ℕ}
-- Only compact field comparisons are required on genuine positive residents.
theorem source_ticket_read (e : (coarse).graph.Edge) (he : 0<weight B e) (j : Fin K) (x : Fields K b)
    (slot : {f : (coarse).graph.Edge // 0<(coarse).graph.width f/(Z).unit ∧ atRawSource B e f} ↪ Fin K)
    (present : ∀f,field x (slot f) 0=field x j 0 ∨ field x (slot f) 1=field x j 0)
    (order : ∀f,field x (slot f) 2<field x j 2 ↔ (tape).rank f.val<(tape).rank e)
    (mass : ∀f,field x (slot f) 3=(coarse).graph.width f.val/(Z).unit)
    (other : ∀a,(∀f,slot f≠a)→field x a 3=0 ∨ (field x a 0≠field x j 0 ∧ field x a 1≠field x j 0)) :
    (ticket B.raw.cap j x).val=(sourceTicket B e he).val := by
  let counted:=sourceTicket_count_atRawSource B e he
  rw [counted]
  apply ticket_read B.raw.cap j x (atRawSource B e) (fun u=>(tape).rank u)
    (fun u=>(coarse).graph.width u/(Z).unit) e slot present order mass other
  exact counted.symm.le.trans (sourceTicket B e he).isLt.le

theorem source_ticket_sum (e : (coarse).graph.Edge) (he : 0<weight B e) (j : Fin K) (x : Fields K b)
    (slot : {f : (coarse).graph.Edge // 0<(coarse).graph.width f/(Z).unit ∧ atRawSource B e f} ↪ Fin K)
    (present : ∀f,field x (slot f) 0=field x j 0 ∨ field x (slot f) 1=field x j 0)
    (order : ∀f,field x (slot f) 2<field x j 2 ↔ (tape).rank f.val<(tape).rank e)
    (mass : ∀f,field x (slot f) 3=(coarse).graph.width f.val/(Z).unit)
    (other : ∀a,(∀f,slot f≠a)→field x a 3=0 ∨ (field x a 0≠field x j 0 ∧ field x a 1≠field x j 0)) :
    (∑a,fee x j a)=(sourceTicket B e he).val := by
  have h:=ticket_sum B.raw.cap j x (atRawSource B e) (fun u=>(tape).rank u)
    (fun u=>(coarse).graph.width u/(Z).unit) e slot present order mass other
  exact h.trans (sourceTicket_count_atRawSource B e he).symm

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
