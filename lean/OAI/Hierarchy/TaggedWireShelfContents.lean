import OAI.Hierarchy.TaggedWirePhysicalTerm
import OAI.Hierarchy.TaggedWireChronologicalMatrix
import OAI.Hierarchy.TaggedWireTurnHeader
import OAI.Hierarchy.TaggedWireTurnData
import OAI.Hierarchy.ProtocolRAMTurnShelf

namespace OAI
/-! # The five physical shelf words of a terminal report -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.Report
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe WireTelescope Computability.VPVNP.BurstRAM PrivateRAM
variable {h d k w R M den W : ℕ} {π : Equiv.Perm (Fin (2^h))} {U : Widths (siteLast h d k+1)}
    (Z : Report π d k w R M den U)
local notation "L" => Z.mount.matrixLayout (siteNumber h d k).injective (publicChord h d k)
local notation "counts" => SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used

/-- A physical read of all five fields at every slot, including every zero-width default.
The two occupied roles are expressed in the original and settled port dictionaries. -/
def ShelfContents (slots n base : ℕ) (out : Memory W)
    (code₀ : Fin (Fintype.card (SettledMatrix.Source Z.edges (Commodity (Fin (2^h)) (Stages h d) k)
      (Columns h d×Fin k)))→Bool→ℕ) (code₁ : Fin Z.edges→Bool→ℕ) : Prop :=
  ∃ (sp : ∀i,Spine (rowGraph (L).edge) ((L).family i).1.1 ((L).routes i) ((L).family i).1.2)
    (posn : Fin n≃TurnShelf.Positions (L).routes) (col : Fin n→Fin 7→ℕ)
    (put : ProtocolRAMTurnShelf.Live col ↪ Fin (siteLast h d k+1)×Fin slots),
    (∀(f : Fin 5) (z : Fin (siteLast h d k+1)×Fin slots),
      out (TurnShelf.addr base z.1 z.2 f)=ProtocolRAMTurnShelf.entry col put f z) ∧
    (∀i,col i 4=counts (posn i).1) ∧
    (∀u : ProtocolRAMTurnShelf.Live col,(put u).1=(sp (posn u.val).1).visit (posn u.val).2) ∧
    ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,
      let q:=posn u.val
      let atRef:=TurnShelf.refAt (L).family (L).edge (L).routes sp q b
      col u.val (if b then 1 else 0)=refRole (L).routes code₀ code₁ q.1 atRef ∧
      col u.val (if b then 3 else 2)=refStart (L).routes counts ((L).nativeOrder Z.enum) q.1 atRef

/-- A subsequent write respecting the occupied shelf segment preserves all five reads. -/
theorem ShelfContents.frame {slots n base : ℕ} {out later : Memory W} {code₀ code₁}
    (c : Z.ShelfContents slots n base out code₀ code₁)
    (kept : ∀x,base≤x→x<base+5*((siteLast h d k+1)*slots)→later x=out x) :
    Z.ShelfContents slots n base later code₀ code₁ := by
  obtain ⟨sp,pos,col,put,read,geometry⟩:=c
  refine ⟨sp,pos,col,put,?_,geometry⟩
  intro f z
  have slot : z.1.val*slots+z.2.val<(siteLast h d k+1)*slots := by
    calc z.1.val*slots+z.2.val < z.1.val*slots+slots := Nat.add_lt_add_left z.2.isLt _
         _ = (z.1.val+1)*slots := (Nat.succ_mul _ _).symm
         _ ≤ _ := Nat.mul_le_mul_right _ z.1.isLt
  have block := Nat.mul_le_mul_right ((siteLast h d k+1)*slots) f.isLt
  rw [Nat.succ_mul] at block
  exact (kept _ (by unfold TurnShelf.addr; omega) (by unfold TurnShelf.addr; omega)).trans (read f z)

end Hierarchy.ProbeStage.CoreBoard.Report
end

end OAI
