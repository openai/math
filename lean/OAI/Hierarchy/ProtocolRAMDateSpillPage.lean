import OAI.Hierarchy.ProtocolRAMTurnReplayed
import OAI.Hierarchy.ProtocolRAMDateSpillZero
import OAI.Hierarchy.ProtocolRAMRowText

namespace OAI
/-! # Widths and cumulative edge loads of one actual dated spill -/
namespace Hierarchy.ProtocolRAM.DateSpill

open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAMPackedRanked ProtocolRAMTurnReplayed
open scoped Fin.CommRing

structure Page where
  floor : ℕ
  old : ℕ
  edges : ℕ
  core : ℕ
  overflow : Bank

namespace Page
variable (P : Page) {W : ℕ}

def amount : Bank := ⟨P.floor,groupBits P.old⟩
def rankStart := P.amount.base+P.amount.size
def load : Bank := ⟨counters P.rankStart (P.edges+P.core),groupBits P.edges⟩
def offsetsStart := endAt P.rankStart (P.edges+P.core) P.edges+P.load.size

theorem amount_room : P.old≤P.amount.size := group_capacity P.old
theorem load_room : P.edges≤P.load.size := group_capacity P.edges
theorem load_end : P.load.base+P.load.size≤P.offsetsStart := by
  have h := rank_room P.rankStart (P.edges+P.core) P.edges
  change counters _ _+_≤endAt _ _ _+_
  unfold ranks at h
  omega

theorem offsetsStart_le : P.offsetsStart≤P.floor+2*(P.old+1)+21*(P.edges+P.core)+3*P.edges+11 := by
  have h:=extent P.rankStart (P.edges+P.core) P.edges
  have a:=bias_words P.old
  have b:=bias_words P.edges
  dsimp only [offsetsStart,rankStart,amount,load,Bank.size] at *
  omega

/-- Decode the original printed source ordinal. Only a commodity row can have
positive mass. The original paid and catalyst rows still occupy their ROM slots. -/
def term (kind index : Expr) : Expr :=
  .branch .eq kind (.lit 1) (.lookup P.overflow index) (.lit 0)

def amounts (W : ℕ) (kind index : Expr) : Procedure W := scan W P.amount.base P.old (P.term kind index)
def amountTime (kind index : Expr) := 4+P.old*(2*(P.term kind index).work+4)

theorem term_fits (kind index : Expr) (kfit : kind.Fits W P.floor) (ifit : index.Fits W P.floor)
    (overflow : P.overflow.Fits W P.floor) : (P.term kind index).Fits W P.floor :=
  ⟨kfit,trivial,⟨overflow,ifit⟩,trivial⟩

theorem run_amounts (kind index : Expr) (m : Memory W)
    (fit : (P.term kind index).Fits W P.floor) (room : P.floor+P.old<2^W) :
    let out:=image P.floor P.old (P.term kind index) m
    (P.amounts W kind index).Exec m out (P.amountTime kind index) ∧
      (∀i : Fin P.old,out (P.amount.base+i.val)=
        if kind.eval m (i.val:Word W)=1 then P.overflow.read m (index.eval m (i.val:Word W)) else 0) ∧
      ∀a,a<P.floor ∨ P.floor+P.old≤a→ out a=m a := by
  intro out
  refine ⟨scan_exec _ _ _ _ fit room,?_,fun a away => ProtocolRAMGeneratedWrite.frame_image P.floor P.old (P.term kind index) m a away⟩
  intro i
  change image P.floor P.old _ m (P.floor+i.val)=_
  rw [ProtocolRAMGeneratedWrite.read_image]
  simp [term,Expr.eval,DescriptorExpr.Comparison.test]

theorem amounts_cheap (W : ℕ) (kind index : Expr) : CheapCode (P.amounts W kind index) := @scan_cheap _ _ _ _
theorem amounts_text (W : ℕ) (kind index : Expr) :
    text (P.amounts W kind index)=Calendar.rowText (P.term kind index) := Calendar.text_scan ..


end Page
end Hierarchy.ProtocolRAM.DateSpill

end OAI
