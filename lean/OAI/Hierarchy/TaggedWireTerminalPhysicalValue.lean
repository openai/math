import OAI.Hierarchy.TaggedWireTurnPhysical
import OAI.Hierarchy.TaggedWireInstalledFinish

namespace OAI
/-! # Evaluating the physical terminal shelf on its five reported fields -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.Report
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open ThreeFlat Routing Tagged WireTelescope Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators

variable {h d k w R M den slots p e W N : ℕ} {π : Equiv.Perm (Row h)} {U : Widths (siteLast h d k+1)}
    (Z : Report π d k w R M den U)
local notation "L" => Z.mount.matrixLayout (siteNumber h d k).injective (publicChord h d k)
local notation "cnt" => SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used
local notation "idx" => (L).nativeOrder Z.enum
local notation "K" => siteLast h d k+1

/-- The signed site weight of the complete terminal report is evaluated by the
actual fixed shelf. Its memory projections and two bit inputs are elementary
reads from the chronological and originally paid words. -/
theorem physical_finish {F : Type*} [Field F] {V : Type} [Fintype V]
    (bit : ℕ×ℕ→V⊕Bool) (aperture : TurnShelf.Aperture p e→V⊕Bool) (input : V→Bool)
    (base : ℕ) (mem : Memory W)
    (sp : ∀i,Spine (rowGraph (L).edge) ((L).family i).1.1 ((L).routes i) ((L).family i).1.2)
    (pos : Fin N≃TurnShelf.Positions (L).routes) (col : Fin N→Fin 7→ℕ)
    (put : ProtocolRAMTurnShelf.Live col ↪ Fin (K)×Fin slots)
    (written : ∀ (f : Fin 5) (a : Fin (K)×Fin slots),mem (TurnShelf.addr base a.1 a.2 f)=ProtocolRAMTurnShelf.entry col put f a)
    (widths : ∀i,col i 4=cnt (pos i).1)
    (site : ∀i : ProtocolRAMTurnShelf.Live col,(put i).1=(sp (pos i.val).1).visit (pos i.val).2)
    (fieldFit : ∀u : ProtocolRAMTurnShelf.Live col,∀f : Fin 5,col u.val (f.castLE (by decide))<2^W)
    (roleFit : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 1 else 0)<2^p)
    (extent : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 3 else 2)+col u.val 4≤2^e)
    (oldCodes : _→Bool→ℕ) (newCodes : Fin Z.edges→Bool→ℕ)
    (role : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 1 else 0)=
      refRole (L).routes oldCodes newCodes (pos u.val).1 (TurnShelf.refAt (L).family (L).edge (L).routes sp (pos u.val) b))
    (start : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 3 else 2)=
      refStart (L).routes cnt idx (pos u.val).1 (TurnShelf.refAt (L).family (L).edge (L).routes sp (pos u.val) b))
    (s : Fin (K)) (v : State U s) (y : ∀i,Fin (2^Z.widthAt i)) (plane : ℕ→ℕ→Bool)
    (prior : ∀i (j : Fin (cnt i)) b (loc : (rowGraph (L).family).vertex i b=s),plane (oldCodes i b) j.val=
      rowBits (L).family cnt (Z.initialState v) ⟨(⟨i,j⟩,b),by cases b <;>exact loc⟩)
    (paid : ∀i (u : Fin ((L).routes i).length) (j : Fin (cnt i)) b,
      (rowGraph (L).edge).vertex (((L).routes i).get u) b=s→
      plane (newCodes (((L).routes i).get u) b) (NativeSlot.start (L).routes cnt idx i u+j.val)=
        (y (((L).routes i).get u)).val.testBit (NativeSlot.start (L).routes cnt idx i u+j.val))
    (headerRead : ∀ t : Fin slots,∀ctrl : TurnShelf.Control p e,
      let u:=TurnShelf.projection ctrl
      Sum.elim input id (bit (TurnShelf.addr base s t u.1,u.2))=(mem (TurnShelf.addr base s t u.1)).val.testBit u.2)
    (fieldRead : ∀d : TurnShelf.Aperture p e,Sum.elim input id (aperture d)=plane d.1.val d.2.val) :
    TypedWiring.value (TurnShelf.physical (F:=F) (r:=slots) base s bit aperture) input=Z.finish s v (Z.ports y s) := by
  rw [TurnShelf.physical_value base s bit aperture input mem headerRead]
  have bitsEq : Sum.elim input id ∘ aperture=fun d=>plane d.1.val d.2.val := funext fieldRead
  rw [bitsEq]
  exact Z.installed_finish base mem sp pos col put written widths site fieldFit roleFit extent oldCodes newCodes
    role start s v y plane prior paid

end Hierarchy.ProbeStage.CoreBoard.Report

end
end OAI
