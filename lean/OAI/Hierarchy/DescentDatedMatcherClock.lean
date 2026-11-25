import OAI.Hierarchy.DescentPackedOrdinaryDateBill
import OAI.Hierarchy.DescentDatedOrdinaryProgram

namespace OAI
/-! # Clock of the date-only matching program on its genuine incoming world -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated
open DescentSixParty DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k groups ℓ w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k)
  (b payload unit ratio profile seats : ℕ) (input : Operands) (floor : ℕ)
set_option quotPrecheck false
local notation "H" => 2^ℓ
local notation "r" => 2^k
local notation "K" => 2^(k+1)
local notation "a" => (⟨H,groups,k,b,A.degree,A.cap,payload,unit,profile,seats⟩ : Ordinary)
local notation "data" => (⟨A.wire,A.z,A.hist⟩ : Measures)
local notation "chooser" => (a).chooser input.roster floor

theorem real_clock (bound : ℕ) (atoms : ∀x : Fin r,(input.atoms x.val).work ≤ bound)
    (pos : 0 < unit) (wide : 2*unit ≤ payload) (word : w ≤ ratio*payload)
    (gate : r+(k+3) ≤ unit) (cable : DescentSignedCableCodec.width A.degree A.cap ≤ unit)
    (weighted : Phase.recordWidth k b (2*A.cap) ≤ unit) (birth : SixBirths.unit (a).shapeAt ≤ unit) :
    (a).ticks gadget A.fieldBits input data w floor*w ≤
      ratio*((Census.multiplier k A.degree A.cap K (max 22 bound)+2*DateBill.extraFactor k A.degree K)*
        DateBill.volumeBits H groups payload unit) :=
  DateBill.rotation_tariff (ℓ:=ℓ) (G:=groups) (w:=w) A chooser b payload unit ratio profile seats
    ((a).prepareAt input.roster floor) (input.ports A.degree) input.actors
    (fun x j=>input.wire x.val j.val) floor input.hubs (fun x=>input.atoms x.val) bound atoms
    pos wide word gate cable weighted rfl birth

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated

end OAI
