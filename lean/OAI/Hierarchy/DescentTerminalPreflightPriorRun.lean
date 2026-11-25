import OAI.Hierarchy.DescentTerminalPreflightRooms
import OAI.Hierarchy.DescentTerminalActorRepack
import OAI.Hierarchy.DescentTerminalPopulationPage
import OAI.Hierarchy.DescentTerminalFrozenCountBank

namespace OAI
/-! # Population and actor fields immediately after the terminal frozen roster -/
namespace Hierarchy.DescentTerminalPriorArena
open DescentSIMDLookup DescentTerminalPrimitiveArena DescentTerminalPointerDigits ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

variable (s : Shape) (groups mPaid mAct paidBits extBits actBits origin : ℕ)
local notation "p0" => pop s groups mPaid paidBits extBits origin
local notation "o1" => actStart s groups mPaid paidBits extBits origin
local notation "a1" => actor s groups mPaid mAct paidBits extBits actBits origin
local notation "next" => start s groups mPaid mAct paidBits extBits actBits origin
local notation "blockRows" => s.rows
variable {wb : ℕ} (paid actorSrc : Fin s.blocks→Bank) (ext : Bank) (nodeBits : ℕ) (pick : Fin s.blocks→Cell actBits→Cell 1)
local notation "popProc" => DescentTerminalPopulation.RAM.issue s.shops groups mPaid paidBits nodeBits extBits origin paid ext wb
local notation "actorProc" => DescentTerminalActorRepack.program pick s.shops groups mAct o1 actorSrc wb
local notation "pCost" => DescentTerminalPopulation.RAM.ticks s.shops groups mPaid paidBits extBits origin paid ext
local notation "aCost" => DescentTerminalActorRepack.ticks (a:=actBits) s.shops groups mAct o1 actorSrc

theorem any_raw (m : Memory wb) (early:Earlier s groups mPaid mAct origin paid actorSrc ext) (room:next<2^wb) :
    let out := final (s:=s) (groups:=groups) (mPaid:=mPaid) (mAct:=mAct) (paidBits:=paidBits)
      (extBits:=extBits) (actBits:=actBits) (origin:=origin) (paid:=paid) (actorSrc:=actorSrc) (ext:=ext)
      (nodeBits:=nodeBits) (pick:=pick) m
    ((popProc).seq actorProc).Exec m out (pCost+aCost) ∧ CheapCode ((popProc).seq actorProc) ∧
      ∀j,j<origin ∨ next≤j → out j=m j := by
  dsimp only
  have full : p0 + blockRows < 2^wb := by
    unfold start actor actStart at room
    omega
  have prior_ : origin ≤ o1 := by unfold actStart pop; omega
  have actual : a1 + blockRows < 2^wb := by unfold start at room;omega
  have fit := paid_fit s groups mPaid mAct paidBits extBits actBits origin paid actorSrc ext early room
  let mid := DescentTerminalPopulation.RAM.done s.shops groups mPaid paidBits nodeBits extBits origin paid ext m
  obtain ⟨exec, good, saved⟩ := DescentTerminalPopulation.RAM.run s.shops groups mPaid paidBits nodeBits extBits origin paid ext m fit full
  have actorsFit (x) : (actorSrc x).Fits wb o1 := by
    have e := early.acEnd x
    have end_ : o1<2^wb := by unfold actor at actual;omega
    exact ⟨Nat.two_pow_pos _, (Nat.le_add_left ..).trans_lt ((e.trans prior_).trans_lt end_),e.trans prior_⟩
  have live:=DescentTerminalActorRepack.any_raw pick s.shops groups mAct o1 actorSrc mid actorsFit actual
  have growth : p0+blockRows ≤ o1:=Nat.le_add_right ..
  have upper : a1+blockRows ≤ next:=Nat.le_add_right ..
  have join_ : o1 ≤ a1:=Nat.le_add_right ..
  refine ⟨exec.then live.1,cheap_seq good live.2.1,?_⟩
  intro j side
  exact (live.2.2 _ (side.imp (fun h=>h.trans_le prior_) (fun h=>upper.trans h))).trans
    (saved _ (side.imp_right (fun h=>growth.trans (join_.trans ((Nat.le_add_right ..).trans (upper.trans h))))))

end
end Hierarchy.DescentTerminalPriorArena

namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open DescentSIMDLookup DescentTerminalPrimitiveArena DescentTerminalPriorArena ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (x:Spec) (base nd:ℕ) (oldPaid actor:Fin x.scalar.blocks→Bank)
    (old:Fin x.scalar.blocks→Fin (2*x.cap)→Bank) (peer total modulo homes:Bank) (boundary:ℕ)
local notation "raw" => (fun (_:Fin x.scalar.blocks) (v:Cell 1)=>v)
local notation "prior" => x.cohortEnd base
local notation "top" => x.primitive base
local notation "next" => actStart x.scalar x.groups x.paidLanes x.paidBits x.externalBits prior
theorem purchased_prior {w:ℕ} (m:Memory w) (boot:x.Before base oldPaid actor old peer total modulo homes boundary)
    (word:x.maskBase base<2^w) :
    let out := DescentTerminalPriorArena.final (s:=x.scalar) (groups:=x.groups) (mPaid:=x.paidLanes) (mAct:=x.actorLanes)
      (paidBits:=x.paidBits) (extBits:=x.externalBits) (actBits:=1) (origin:=prior) (paid:=oldPaid) (actorSrc:=actor)
      (ext:=x.census base) (nodeBits:=nd) (pick:=raw) m
    let cut:=DescentTerminalPopulation.RAM.issue x.scalar.shops x.groups x.paidLanes x.paidBits nd x.externalBits prior oldPaid (x.census base) w
    let issue:=DescentTerminalActorRepack.program raw x.scalar.shops x.groups x.actorLanes next actor w
    (cut.seq issue).Exec m out (DescentTerminalPopulation.RAM.ticks x.scalar.shops x.groups x.paidLanes x.paidBits x.externalBits prior oldPaid (x.census base) +
      DescentTerminalActorRepack.ticks (a:=1) x.scalar.shops x.groups x.actorLanes next actor) ∧
      CheapCode (cut.seq issue) ∧ ∀j,j<prior ∨ top≤j → out j=m j := by
  have earlier:=x.earlier_population base oldPaid actor old peer total modulo homes boundary boot
  have room:top<2^w:=by obtain ⟨a,b,c,d,e,f,g,h,j⟩:=x.layers base;omega
  exact DescentTerminalPriorArena.any_raw x.scalar x.groups x.paidLanes x.actorLanes x.paidBits x.externalBits 1 prior
    oldPaid actor (x.census base) nd raw m earlier room

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
