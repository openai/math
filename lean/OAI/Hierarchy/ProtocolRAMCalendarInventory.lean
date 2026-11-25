import OAI.Hierarchy.ProtocolRAMCalendarSegments
import OAI.Hierarchy.ProbeOuterAccount

namespace OAI
/-! # Temporal views of the physical inventory and its signed posting archive -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open AdaptiveProbe AdaptiveProbe.OuterBank
open scoped BigOperators Classical
noncomputable section
variable {w q d : ℕ} {I : Type*} [Fintype I]

/-- A phase's actual retained stock bank is selected by the public calendar;
cash is the fixed starting payment plus the signed price of the physical
width words issued up to that program point. -/
structure AccountColumns (I : Type*) where
  payloadWidth : ℕ
  stockAt : Attempt → I → ℕ
  charges : Attempt → ℕ
  widthAt : (a : Attempt) → Fin (charges a) → ℕ
  priceKeyAt : (a : Attempt) → Fin (charges a) → ℕ
  unitPrice : (a : Attempt) → Fin (charges a) → ℕ → ℝ
  initialCharge : ℝ
  payload : I → ℕ
  box : I → ℝ
  coefficient : I → ℝ
  a : ℝ
  M : ℝ

structure Inventory (I : Type*) where
  bits : I → ℕ
  paid : ℝ

def AccountColumns.bank (A : AccountColumns I) : OuterBank I (Inventory I) :=
  ⟨Inventory.bits,Inventory.paid,A.payload,A.box,A.coefficient,A.a,A.M⟩

def AccountColumns.read (A : AccountColumns I) (a : Attempt) (mem : Memory w) : Inventory I :=
  ⟨fun i => (mem (A.stockAt a i)).val, A.initialCharge +
    (∑ r, ((mem (A.widthAt a r)).val:ℝ)*A.unitPrice a r (mem (A.priceKeyAt a r)).val)/A.payloadWidth⟩

def AccountColumns.trial (A : AccountColumns I) (C : Chart w q d) (mem : Memory w) (j h : ℕ) :=
  A.read (.outer j h) (trialState C mem j h)

def AccountColumns.inner (A : AccountColumns I) (C : Chart w q d) (mem : Memory w) (j h k b : ℕ) :=
  A.read (.inner j h k b) (innerState C mem j h k b)

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
