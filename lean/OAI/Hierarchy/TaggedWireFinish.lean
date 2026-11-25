import OAI.Hierarchy.TaggedWireTurnMatrix
import OAI.Hierarchy.TaggedWireTurnHeader
import OAI.Hierarchy.TaggedWireExitCheck
import OAI.Hierarchy.TaggedWirePhysicalTerm

namespace OAI
/-! # The finite terminal shelf at the actual reported edge words -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open scoped Classical

/-- Casts from the receipt change only certified word widths. In particular
deleting a zero-width native row never introduces a new field read. -/
theorem row_cast {K n : ℕ} (ends : Fin n→Chord K) (u v : Fin n→ℕ) (nv : u=v)
    {T : Widths K} (out : installedWidths ends v=T) (s : Fin K) (y : ∀i,Fin (2^v i)) :
    cast (congrArg (fun U=>State U s) ((congrArg (installedWidths ends) nv).trans out).symm)
      (cast (congrArg (fun U=>State U s) out) (readEdges ends v y s)) =
      readEdges ends u (fun j=>Fin.cast (congrArg (fun z=>2^z) (congrFun nv j).symm) (y j)) s := by
  subst v
  subst T
  rfl

end Hierarchy.WireTelescope
namespace Hierarchy.ProbeStage.CoreBoard.Report
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open ThreeFlat Routing Tagged WireTelescope
open scoped Classical BigOperators

variable {h d k w R M den slots p e W : ℕ} {π : Equiv.Perm (Row h)} {U : Widths (siteLast h d k+1)}
    (Z : Report π d k w R M den U)
local notation "L" => Z.mount.matrixLayout (siteNumber h d k).injective (publicChord h d k)
local notation "counts" => SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used
local notation "number" => (L).nativeOrder Z.enum

def initialState {s : Fin (siteLast h d k+1)} (v : State U s) :=
  cast (congrArg (fun u=>State u s)
    ((Z.receipt.old_width (siteNumber h d k).injective (publicChord h d k)).trans Z.ledger).symm) v

def finalData (y : ∀i,Fin (2^Z.widthAt i)) : ∀i,Fin (2^routeLoad (L).routes counts i) :=
  fun i=>Fin.cast (congrArg (fun z=>2^z)
    (congrFun (Z.receipt.native_width (siteNumber h d k).injective (publicChord h d k)) i).symm) (y i)

/-- The two scalar inputs to each emitted comparison are literal bits of
the preceding party state and the true final edge words. -/
def readRef (s : Fin (siteLast h d k+1)) (v : State U s) (y : ∀i,Fin (2^Z.widthAt i)) (q : Bundle counts) :=
  readTurn (rowGraph (L).edge) (rowGraph (L).family) (L).routes counts
    (NativeSlot.allocation (L).routes counts number) q s
      (rowBits (L).family counts (Z.initialState v),
       (bitGraph (rowGraph (L).edge) (routeLoad (L).routes counts)).atVertex
         (wordBitsEquiv (routeLoad (L).routes counts) (Z.finalData y)) s)

universe u

private theorem compose_casts {A B C : Type u} (ab : A=B) (bc : B=C) (ac : A=C) (x : A) :
    cast bc (cast ab x)=cast ac x := by
  subst B
  subst C
  rfl

theorem finish_on_words {F : Type*} [Field F] (s : Fin (siteLast h d k+1))
    (v : State U s) (y : ∀i,Fin (2^Z.widthAt i)) :
    Z.finish (F:=F) s v (Z.ports y s)=chordRouter (L).family (L).edge (L).routes counts number
      (fun _i=>(L).paths _) s (Z.initialState v) (readEdges (L).edge (routeLoad (L).routes counts) (Z.finalData y) s) := by
  let inj := (siteNumber h d k).injective
  let pad := publicChord h d k
  refine (rebase_apply Z.ledger rfl (Z.receipt.matrix (F:=F) inj pad Z.enum)
    s v (Z.ports y s)).trans ?_
  refine (rebase_apply (Z.receipt.old_width inj pad) (Z.receipt.new_width inj pad)
    ((L).operator (F:=F) Z.fixed Z.stock Z.reserved Z.used number) s _ _).trans ?_
  apply congrArg₂ (chordRouter (F:=F) (L).family (L).edge (L).routes counts number (fun i=>(L).paths _) s)
  · unfold initialState
    exact compose_casts _ _ _ v
  · unfold ports finalData
    exact row_cast (T:=Z.output) (L).edge (routeLoad (L).routes counts) Z.widthAt
      (Z.receipt.native_width inj pad) (Z.receipt.reported_width pad) s y

/-- Fixed physical terminal network at one party. Its heap addresses and native
registers are the same `m` from the reported five-field shelf; only the
ordinary input bits and per-field readbacks enter the interface. -/
theorem fixed_finish {F : Type*} [Field F] (s : Fin (siteLast h d k+1))
    (v : State U s) (y : ∀i,Fin (2^Z.widthAt i)) (header : Fin slots→TurnShelf.RowData p e)
    (words : TurnShelf.Aperture p e→Bool) (base : ℕ) (m : Computability.VPVNP.BurstRAM.Memory W)
    (read : ∀t f,(m (TurnShelf.addr base s t f)).val=TurnShelf.rowField (header t) f)
    (room : ∀t b,((header t).start b).val+(header t).live.val≤2^e)
    (seat : TurnShelf.Live (L).family (L).edge (L).routes counts s ↪ Fin slots)
    (live : ∀j,(header (seat j)).live.val=counts j.val.1)
    (empty : ∀t,t∉Set.range seat→(header t).live.val=0)
    (two : ∀i b (j : Fin (counts i.val.1)),
      TurnShelf.reads (header (seat i)) words b (j.cast (live i).symm) (room (seat i) b)=
      Z.readRef s v y ⟨i.val.1,j⟩ (TurnShelf.hand (L).family (L).edge (L).routes s i.val b)) :
    TypedWiring.value (TurnShelf.network F slots p e) (TurnShelf.nativeView base s m words)=
      Z.finish s v (Z.ports y s) := by
  rw [TurnShelf.nativeView_eq base s m header words read,Z.finish_on_words]
  exact TurnShelf.route_matrix (L).family (L).edge (L).routes counts number (fun i=>(L).paths _)
    F s (Z.initialState v) (readEdges _ _ (Z.finalData y) s) header words room seat live empty
    (by simpa only [readRef,rowBits_readEdges] using two)

end Hierarchy.ProbeStage.CoreBoard.Report

end
end OAI
