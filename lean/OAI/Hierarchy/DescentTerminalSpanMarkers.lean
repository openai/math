import OAI.Hierarchy.DescentTerminalSpanCounts
import OAI.Hierarchy.DescentTerminalHeaderPrefixAny
import OAI.Hierarchy.DescentTerminalHeaderScatterRAM

namespace OAI
/-! # Mark true allocated beginnings by one cheap overwrite at each site -/
namespace Hierarchy.DescentTerminalSpanBook
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalRecipeRows DescentTerminalBinPack
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr DescentTerminalHeaderScatter
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w S W q : ℕ}

structure MarkerBanks where
  first : Bank
  half : Bank
  lane : Bank
  mark : Bank

namespace MarkerBanks
def startExpr (L : MarkerBanks) : Expr := .op .add (.lit L.mark.base) (.lookup L.first (.lookup L.half .row))
def program (w src rows S : ℕ) (L : MarkerBanks) :=
  (scan w L.mark.base rows (.lit 0)).seq (DescentTerminalHeaderScatter.program w src S (bounded L.mark L.startExpr) (.lit 1) L.lane)
def clear (L : MarkerBanks) (rows : ℕ) (m : Memory w) := image L.mark.base rows (.lit 0) m
def result (L : MarkerBanks) (src S rows : ℕ) (m : Memory w) :=
  imageAt src S (bounded L.mark L.startExpr) (.lit 1) L.lane (clear L rows m)
def time (L : MarkerBanks) (rows S : ℕ) := (4+rows*(2*Expr.work (.lit 0)+4))+cost S (bounded L.mark L.startExpr) (.lit 1) L.lane

structure Room (L : MarkerBanks) (w src rows S : ℕ) : Prop where
  mark : L.mark.Fits w src
  endMark : rows≤L.mark.size
  first : L.first.Fits w L.mark.base
  half : L.half.Fits w L.mark.base
  lane : L.lane.Fits w L.mark.base
  ready : (stage (bounded L.mark L.startExpr) (.lit 1) L.lane).Fits w src
  endAt : src+2*S<2^w
def Fixed (L : MarkerBanks) (S : ℕ) (m : Memory w) :=
  ∀(i : Fin S) (j : Fin 2),L.lane.read m ((field i j).val:Word w)=(j.val:Word w)

private theorem clear_then_mark (a b : Procedure w) (m u v : Memory w) (x y : ℕ)
    (clearRun : a.Exec m u x) (clearCheap : CheapCode a) (write : b.Exec u v y ∧ CheapCode b) :
    (a.seq b).Exec m v (x+y) ∧ CheapCode (a.seq b) :=
  ⟨Procedure.Exec.then (A:=a) (B:=b) clearRun write.1,
    @cheap_seq w a b clearCheap write.2⟩

theorem any (L : MarkerBanks) (src S rows : ℕ) (m : Memory w) (f : L.Room w src rows S) (positive:0<w)
    (literal : L.Fixed S m) :
    (program w src rows S L).Exec m (L.result src S rows m) (time L rows S) ∧ CheapCode (program w src rows S L) := by
  have endAt:=f.endAt; have size:=f.mark.2.2;have span:=f.endMark
  have c : (scan w L.mark.base rows (.lit 0)).Exec m (clear L rows m)
      (4+rows*(2*Expr.work (.lit 0)+4)) :=
    scan_exec L.mark.base rows (.lit 0) m trivial (by omega)
  have low {a} (ha:a<L.mark.base) : clear L rows m a=m a:=by simp [clear,image,fillSegment,not_le.mpr ha]
  have lane (i : Fin S) (j : Fin 2) :
      L.lane.read (clear L rows m) ((field i j).val : Word w) = (j.val : Word w) := by
    rw [←literal i j]
    apply low
    have bound := f.lane.2.2
    have off := Nat.mod_lt ((field i j).val : Word w).val f.lane.1
    omega
  unfold program result time
  apply clear_then_mark (scan w L.mark.base rows (.lit 0))
    (DescentTerminalHeaderScatter.program w src S (bounded L.mark L.startExpr) (.lit 1) L.lane)
    m (clear L rows m) _ _ _
  · exact @c
  · exact @scan_cheap w L.mark.base rows (.lit 0)
  · exact DescentTerminalHeaderScatter.exec_any L.mark L.lane L.startExpr (.lit 1) (clear L rows m)
      src positive f.mark f.ready f.endAt lane

theorem truth (L : MarkerBanks) (src rows : ℕ) (sites : Fin S→Site) (m : Memory w) (f : L.Room w src rows S)
    (cap : ∀i:Fin S,DescentTerminalBinPack.first W (counts (q:=q) sites) i<rows)
    (readFirst : ∀i:Fin S,L.first.read m (i.val:Word w)=((DescentTerminalBinPack.first W (counts (q:=q) sites) i):Word w))
    (half : ∀i:Fin S,L.half.read m ((field i 0).val:Word w)=(i.val:Word w)) (z : Fin rows) :
    L.result src S rows m (L.mark.base+z.val)=(DescentTerminalSpanBook.mark (W:=W) (q:=q) sites z.val:Word w) := by
  let clearM:=clear L rows m
  let n (i:Fin S):=DescentTerminalBinPack.first W (counts (q:=q) sites) i
  have ends:=f.endAt;have markFits:=f.mark.2.2
  have before (b:Bank) (safe:b.Fits w L.mark.base) (x:Word w) : b.read clearM x=b.read m x:=by
    have low:=safe.2.2;have gr:=Nat.mod_lt x.val safe.1
    simp [clearM,clear,Bank.read,image,fillSegment,not_le.mpr (show b.base+x.val%b.size<L.mark.base by omega)]
  have placed (i:Fin S) : ((bounded L.mark L.startExpr).eval clearM ((field i 0).val:Word w)).val=L.mark.base+n i:=by
    have value : L.startExpr.eval clearM ((field i 0).val : Word w) =
        ((L.mark.base + n i : ℕ) : Word w) := by
      simp [MarkerBanks.startExpr,Expr.eval,RowOp.opcode,BinaryOp.eval,before _ f.first,before _ f.half,half,readFirst,n]
    have inBank : n i < L.mark.size := (cap i).trans_le f.endMark
    rw [bounded_exact L.mark L.startExpr clearM _ f.mark (by omega) inBank value,
      value,Fin.val_cast_of_lt (show L.mark.base + n i < 2^w by omega)]
  apply published
  · intro i hi
    change ((bounded L.mark L.startExpr).eval clearM _).val=_ at hi
    rw [placed] at hi
    have eqn:n i=z.val:=Nat.add_left_cancel hi
    simp [DescentTerminalSpanBook.mark,show ∃v,DescentTerminalBinPack.first W (counts (q:=q) sites) v=z.val from ⟨i,eqn⟩,actual,Expr.eval]
  · by_cases live:∃i,n i=z.val
    · obtain ⟨i,hi⟩:=live
      right;exact ⟨i,by change ((bounded L.mark L.startExpr).eval clearM _).val=_;rw [placed,hi]⟩
    · left;have hist : L.mark.base+z.val<src:= by have:=z.isLt;have:=f.endMark;omega
      simp [image,clear,fillSegment,not_le.mpr hist,z.isLt,Expr.eval,DescentTerminalSpanBook.mark,live,n]

end MarkerBanks
end
end Hierarchy.DescentTerminalSpanBook

end OAI
