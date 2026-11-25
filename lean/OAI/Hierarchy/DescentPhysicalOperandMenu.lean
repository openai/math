import OAI.Hierarchy.DescentPhysicalOperandLaws
import OAI.Hierarchy.DescentPhysicalResetAtlas
import OAI.Hierarchy.DescentResetRetainedPriorBanks
import OAI.Hierarchy.DescentResetWindowColumns
import OAI.Hierarchy.DescentPreparedRootInputs

namespace OAI
/-! Native operands of the reset ROM. Only the selected date's earlier numeric bank offsets are needed. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSIMDLookup DescentPackedColony DescentDenseHostOrder
open DescentFallbackPeriod DescentFallbackPeriod.Projected DescentResetOperandSetup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} (z : a.Atlas) (roots : a.RootInputs)
local notation "v" => a.successor
local notation "C" => (v).setup
local notation "B" => (v).middle
local notation "r" => (B).rootDepth
local notation "cap" => a.c/2

def publicOperands (payload : ℕ) :=
  Chart.publicMenu z.board a.ports r cap roots.Ht (C).rotorBits (C).queryBits (C).lanes
    z.groupDigits (C).retained.args (C).retained.nodes z.packet a.depthCut z.C payload

structure OperandMenu where
  previousMeta : ℕ
  previousArguments : ℕ
  payload : ℕ
  initial : Bool
  inputCount : (C).fallbackInputs=Chart.publicOperands a.ports r cap (B).rotorBits
  wordSize : (C).fallbackBits=(C).rotorBits
  nodes : (C).placement.shapes=(roster z.board r roots.Ht).card
  donors : (C).retained.donors=2^r
  capacity : (C).oldCap=cap

namespace OperandMenu
variable {z roots} (m : OperandMenu z roots)
def tables : (C).Laws :=by
  let p:=publicOperands z roots m.payload
  have fit : (C).Format (n:=(B).rotorBits) p:=
    ⟨rfl,rfl,rfl,m.wordSize,m.inputCount⟩
  exact fit.laws z.board

def retained : Fin (C).retained.sources→Bank :=
  if m.initial then (C).retained.seedPrior m.previousMeta m.previousArguments
  else (C).retained.laterPrior m.previousMeta m.previousArguments

def keep (j : Fin (C).placement.shapes) : Bool :=
  match ActorSetup.shapeAt z.board r roots.Ht (j.cast m.nodes) with
  | .trunk false _ => true
  | _ => false

def target (j : Fin (C).placement.shapes) : Option ℕ:=
  match ActorSetup.shapeAt z.board r roots.Ht (j.cast m.nodes) with
  | .trunk false (_,mark)=>some (DescentFallbackShapeTable.cell r mark)
  | _=>none

def matrixPacket (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y w : ℕ) : Expr:=
  let rc:=a.rootPhase sh floor count hub g Y roots w
  let book:=atlasBook z sh floor count hub g Y roots w
  let first : DescentResetHostSize.Code r:=
    ⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩
  rc.gatheredOperand book (false,.inl (first,.inl false))

def banks (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y w : ℕ) : (C).Sources :=
  let p:=a.stencilPhase sh floor count hub g Y
  let rc:=a.rootPhase sh floor count hub g Y roots w
  let dir:=(v).actor.directory ((B).stop (a.rebased floor))
  {old:=m.retained,matrix:=⟨p.saved,0⟩,count:=dir.count,inverse:=dir.inverse,primary:=m.keep,which:=m.target,
   window:=matrixPacket (z:=z) (roots:=roots) sh floor count hub g Y w,
   signed:=fun j=>
     let pair : Fin (C).retained.donors×Fin (2*(C).oldCap):=finProdFinEquiv.symm j
     .lookup (bankAt rc.stencil rc.tapped p.S.t a.ports rc.signedEnd (B).signedHosts (2^p.S.c) (B).signedLanes
       (.inr (pair.2.cast (congrArg (2*·) m.capacity),pair.1.cast m.donors))) .row}

/-- The guarded old target window is an actual previously gathered root operand. -/
theorem window_fits (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y w : ℕ)
    (safe : (a.rootPhase sh floor count hub g Y roots w).PreparedFits (atlasBook z sh floor count hub g Y roots w))
    (prior : (a.rootPhase sh floor count hub g Y roots w).preparedEnd (atlasBook z sh floor count hub g Y roots w)≤
      (v).operandFloor (a.rebased floor)) :
    (m.banks sh floor count hub g Y w).window.Fits w ((v).operandFloor (a.rebased floor)) :=by
  apply ProtocolRAMGeneratedWrite.fits_mono _ prior
  exact (a.rootPhase sh floor count hub g Y roots w).gathered_fits _ safe _

theorem old_at (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y w : ℕ) :
    (m.banks sh floor count hub g Y w).old=m.retained ∧
      (m.banks sh floor count hub g Y w).matrix.base=(a.stencilPhase sh floor count hub g Y).saved :=⟨rfl,rfl⟩

end OperandMenu
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
