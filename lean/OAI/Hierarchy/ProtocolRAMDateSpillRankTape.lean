import OAI.Hierarchy.ProtocolRAMDateSpillPage
import OAI.Hierarchy.ProtocolRAMDateSpillRank
import OAI.Hierarchy.ProtocolRAMRankGatherCost
import OAI.Hierarchy.ProtocolRAMTurnRankTextSize

namespace OAI
/-! # Sequential placement of the actual dated spill counters -/
noncomputable section
namespace Hierarchy.ProtocolRAM.DateSpill
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAMPackedRanked ProtocolRAMDateSpillRank ProtocolRAMTurnReplayed

structure RankTape where
  first : ℕ
  old : ℕ
  edges : ℕ
  core : ℕ
  overflow : ℕ→Bank
  accounts : RouteSettlement.Banks
  kind : Expr
  index : Expr

namespace RankTape
variable (A : RankTape)
def zero : Bank := ⟨A.first,groupBits A.edges⟩
def stride := 2*(A.old+1)+21*(A.edges+A.core)+3*A.edges+11
def stop (j : ℕ) := A.first+A.zero.size+j*A.stride
def page (j : ℕ) : Page := ⟨A.stop j,A.old,A.edges,A.core,A.overflow j⟩

theorem page_end (j : ℕ) : (A.page j).offsetsStart≤A.stop (j+1) := by
  have h := (A.page j).offsetsStart_le
  have eq : A.stop (j+1)=A.stop j+A.stride := by simp [stop,Nat.succ_mul,Nat.add_assoc]
  rw [eq]
  simpa only [page,stride,Nat.add_assoc] using h

def one (W j : ℕ) : Procedure W :=
  let P:=A.page j
  (P.amounts W A.kind A.index).seq
    (procedure W P.rankStart A.edges A.core (dateBanks A.accounts P.overflow A.zero) A.zero)

def oneTime (j : ℕ) :=
  (A.page j).amountTime A.kind A.index+(66+539*(A.edges+A.core)+6*A.edges)

def program (A : RankTape) (W : ℕ) : ℕ→Procedure W
  | 0=>clear W A.zero A.edges
  | j+1=>(program A W j).seq (A.one W j)

def ticks (A : RankTape) : ℕ→ℕ
  | 0=>4+6*A.edges
  | j+1=>ticks A j+A.oneTime j

private theorem prefix_cheap (W edges core scratch rows groups counters ranks : ℕ)
    (banks : RouteSettlement.Banks) (weight key : Bank) :
    CheapCode (ProtocolRAMTurnPrefix.program W edges core scratch rows groups counters ranks banks weight key) :=
  cheap_seq (cheap_seq (scan_cheap _ _ _ _) (scan_cheap _ _ _ _))
    (cheap_seq (cheap_seq (ProtocolRAMRankCheap.gather _ _ _ _ _ _ _) (scan_cheap _ _ _ _))
      (TaggedShorterCommonScan.cheap _ _ _ _ _ _))

theorem cheap (W j : ℕ) : CheapCode (A.program W j) := by
  induction j with
  | zero => exact @clear_cheap W A.zero A.edges
  | succ j ih =>
    let P := A.page j
    let lo := P.rankStart
    let n := A.edges+A.core
    let banks := dateBanks A.accounts P.overflow A.zero
    have ranked : CheapCode (procedure W lo A.edges A.core banks A.zero) :=
      @prefix_cheap W A.edges A.core
        (ProtocolRAMTurnReplayed.scratch lo n) (ProtocolRAMTurnReplayed.rows lo n)
        (ProtocolRAMTurnReplayed.groups lo n) (ProtocolRAMTurnReplayed.counters lo n)
        (ProtocolRAMTurnReplayed.ranks lo n A.edges) (ProtocolRAMTurnReplayed.original banks A.zero)
        (ProtocolRAMTurnReplayed.weight lo n) (ProtocolRAMTurnReplayed.key lo n)
    exact @cheap_seq W (A.program W j) (A.one W j) @ih
      (@cheap_seq W (P.amounts W A.kind A.index) (procedure W lo A.edges A.core banks A.zero)
        (@Page.amounts_cheap P W A.kind A.index) @ranked)

theorem time_eq (j : ℕ) :
    A.ticks j=4+6*A.edges+j*(4+A.old*(2*(A.kind.work+A.index.work+8)+4)+66+539*(A.edges+A.core)+6*A.edges) := by
  induction j with
  | zero=>simp [ticks]
  | succ j ih=>
    change A.ticks j+A.oneTime j=_
    rw [ih,Nat.succ_mul j _]
    simp only [oneTime,Page.amountTime,Page.term,page,Expr.work]
    ring

theorem text_eq (W j : ℕ) :
    text (A.program W j)=15+j*(11+4*(A.kind.work+A.index.work+8)+1137) := by
  induction j with
  | zero=>simpa only [program,Nat.zero_mul,Nat.add_zero] using clear_text W A.zero A.edges
  | succ j ih=>
    change text ((A.program W j).seq (A.one W j))=_
    rw [text_seq,ih,one,text_seq,Page.amounts_text,ProtocolRAMTurnText.rank_text_exact]
    simp only [Calendar.rowText,Page.term,Expr.work,Nat.succ_mul]
    ring

end RankTape
end Hierarchy.ProtocolRAM.DateSpill

end
end OAI
