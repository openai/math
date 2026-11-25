import OAI.Hierarchy.TaggedWireFinish
import OAI.Hierarchy.TaggedWireTurnSparseMatrix
import OAI.Hierarchy.TaggedWireTurnData

namespace OAI
/-! # Signed terminal gate on the actual committed five-column CPU output -/
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

/-- The native receipt is indexed by the original chronological rows. It suffices
to read the old site and the original uncompressed reported edge at their public
role numbers and original low bit positions. All equality gates consume those
actual private bits. The sparse output, including inactive roles, is shared
among all local factors and payload choices. -/
theorem installed_finish {F : Type*} [Field F] (base : ℕ) (mem : Memory W)
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
        (y (((L).routes i).get u)).val.testBit (NativeSlot.start (L).routes cnt idx i u+j.val)) :
    TypedWiring.value (TurnShelf.network F slots p e)
      (TurnShelf.nativeView base s mem (fun d=>plane d.1.val d.2.val))=Z.finish s v (Z.ports y s) := by
  rw [Z.finish_on_words]
  apply TurnShelf.scattered_matrix (L).family (L).edge (L).routes cnt sp pos col put widths site
    F base mem idx (fun i=>(L).paths _) written fieldFit roleFit extent s (Z.initialState v)
    (readEdges _ _ (Z.finalData y) s)
  intro u localSite b j address roleRead startRead
  rw [roleRead,startRead,role,start,rowBits_readEdges]
  have whereAt := (site u).symm.trans localSite
  have valid := valid_pair (L).family (L).edge (L).routes (pos u.val).1 (sp (pos u.val).1) (pos u.val).2
  rw [whereAt] at valid
  have choice : ValidRef (L).family (L).edge (L).routes (pos u.val).1 s
      (TurnShelf.refAt (L).family (L).edge (L).routes sp (pos u.val) b) := by
    cases b
    · exact valid.1
    · exact valid.2
  apply read_private (L).family (L).edge (L).routes cnt idx (pos u.val).1 j s _ choice
    (rowBits (L).family cnt (Z.initialState v)) (Z.finalData y) oldCodes newCodes plane
  · exact prior _ j
  · exact fun q b loc=>paid _ q j b loc

end Hierarchy.ProbeStage.CoreBoard.Report

end
end OAI
