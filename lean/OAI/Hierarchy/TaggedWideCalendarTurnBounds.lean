import OAI.Hierarchy.TaggedWireInstalledFinish
import OAI.Hierarchy.TaggedWireTurnStartRead

namespace OAI
/-! # Capacity and native word size of all five stored turn fields -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.Report
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open ThreeFlat Routing Tagged WireTelescope Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators
variable {h d k w R M den N : ℕ} {π : Equiv.Perm (Row h)} {U : Widths (siteLast h d k+1)}
    (Z : Report π d k w R M den U)
local notation "L" => Z.mount.matrixLayout (siteNumber h d k).injective (publicChord h d k)
local notation "cnt" => SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used
local notation "idx" => (L).nativeOrder Z.enum
variable (sp :
      let layout := Z.mount.matrixLayout (siteNumber h d k).injective (publicChord h d k)
      ∀i,Spine (rowGraph layout.edge) (layout.family i).1.1 (layout.routes i) (layout.family i).1.2)
    (pos : Fin N≃TurnShelf.Positions
      (Z.mount.matrixLayout (siteNumber h d k).injective (publicChord h d k)).routes)
    (col : Fin N→Fin 7→ℕ)

theorem turn_extent (cap : ℕ) (old : ∀i,cnt i≤cap) (new : ∀a,Z.widthAt a≤cap)
    (widths : ∀i,col i 4=cnt (pos i).1)
    (start : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 3 else 2)=
      refStart (L).routes cnt idx (pos u.val).1 (TurnShelf.refAt (L).family (L).edge (L).routes sp (pos u.val) b)) :
    ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 3 else 2)+col u.val 4≤cap := by
  intro u b
  have positive : 0<cnt (pos u.val).1 := by rw [←widths]; exact Nat.pos_of_ne_zero u.property
  have source := valid_pair (L).family (L).edge (L).routes (pos u.val).1 (sp (pos u.val).1) (pos u.val).2
  have valid : ValidRef (L).family (L).edge (L).routes (pos u.val).1 ((sp (pos u.val).1).visit (pos u.val).2)
      (TurnShelf.refAt (L).family (L).edge (L).routes sp (pos u.val) b) := by
    cases b
    · exact source.1
    · exact source.2
  rw [start u b,widths u.val]
  apply ref_extent (L).family (L).edge (L).routes cnt idx _ _ _ valid positive cap (old _)
  intro a
  exact (congrFun (Z.receipt.native_width (siteNumber h d k).injective (publicChord h d k)) a).le.trans (new a)

theorem turn_role_fits (p : ℕ) (oldCodes : _→Bool→ℕ) (newCodes : Fin Z.edges→Bool→ℕ)
    (before : ∀i b,oldCodes i b<2^p) (after : ∀a b,newCodes a b<2^p)
    (role : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 1 else 0)=
      refRole (L).routes oldCodes newCodes (pos u.val).1 (TurnShelf.refAt (L).family (L).edge (L).routes sp (pos u.val) b)) :
    ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 1 else 0)<2^p := by
  intro u b
  rw [role]
  rcases TurnShelf.refAt (L).family (L).edge (L).routes sp (pos u.val) b with side|⟨j,side⟩
  · exact before _ _
  · dsimp only [refRole]
    split
    · exact after _ _
    · exact Nat.two_pow_pos _

/-- All five fields fit the real native word. The two binary roles use the
role aperture; the start rows and width use the funded capacity. -/
theorem turn_words {n W p cap : ℕ} (col : Fin n→Fin 7→ℕ) (pFits : p≤W) (capFits : cap<2^W)
    (roles : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 1 else 0)<2^p)
    (extent : ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 3 else 2)+col u.val 4≤cap) :
    ∀u : ProtocolRAMTurnShelf.Live col,∀f : Fin 5,col u.val (f.castLE (by decide))<2^W := by
  intro u f
  have h₀ := (roles u false).trans_le (Nat.pow_le_pow_right (by decide : 0<2) pFits)
  have h₁ := (roles u true).trans_le (Nat.pow_le_pow_right (by decide : 0<2) pFits)
  have h₂ : col u.val 2+col u.val 4≤cap :=extent u false
  have h₃ : col u.val 3+col u.val 4≤cap :=extent u true
  fin_cases f
  · exact h₀
  · exact h₁
  · exact (Nat.le_add_right _ _).trans_lt (h₂.trans_lt capFits)
  · exact (Nat.le_add_right _ _).trans_lt (h₃.trans_lt capFits)
  · exact (Nat.le_add_left _ _).trans_lt (h₂.trans_lt capFits)

end Hierarchy.ProbeStage.CoreBoard.Report

end
end OAI
