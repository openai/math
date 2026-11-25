import OAI.Hierarchy.DescentTerminalScanFacts
import OAI.Hierarchy.DescentTerminalProposalCheck
import OAI.Hierarchy.DescentTerminalDenseWindowRAM
import OAI.Hierarchy.DescentTerminalBinSliceCheap
import OAI.Hierarchy.DescentTerminalScalarDispatch

namespace OAI
/-! # One fixed native program for both data transposes and terminal scalar keys -/
namespace Hierarchy.DescentTerminalChipRuntime
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w N slots : ℕ}

structure Banks where
  index : Bank
  formats : Bank
  raw : Bank
  menuStart : Bank
  highField : Bank
  denseROM : Bank
  gate : Bank
  joinedX : Bank
  pointer : Bank
  routeROM : Bank
  scalar : DescentTerminalScalarDispatch.Layout
  xWords : Bank
  ySlices : Bank
  empty : ℕ

def dense (L : Banks) := DescentTerminalDenseWindowRAM.row L.index L.formats L.raw L.menuStart L.highField L.denseROM
def route (L : Banks) := sliceLookup L.gate L.joinedX L.pointer L.routeROM
def key (L : Banks) := DescentTerminalScalarDispatch.fetch L.scalar L.empty

structure Layout where
  first : ℕ
  logRows : ℕ

def Layout.width (A : Layout) := 2^A.logRows
def Layout.x (A : Layout) : Bank := ⟨A.first,A.logRows⟩
def Layout.xCheck (A : Layout) := A.first+A.width
def Layout.y (A : Layout) : Bank := ⟨A.first+2*A.width+1,A.logRows⟩
def Layout.yCheck (A : Layout) := A.first+3*A.width+1
def Layout.keys (A : Layout) := A.first+4*A.width+2

structure Room (A : Layout) (L : Banks) (w N slots : ℕ) : Prop where
  inputDense : (dense L).Fits w A.first
  inputRoute : (route L).Fits w A.first
  inputKey : (key L).Fits w A.first
  x : L.xWords.Fits w A.first
  y : L.ySlices.Fits w A.first
  xCap : N≤L.xWords.size
  yCap : N≤L.ySlices.size
  count : N≤A.width
  last : A.keys+slots<2^w

def program (A : Layout) (L : Banks) (w N slots : ℕ) : Procedure w :=
  ((((scan w A.x.base N (dense L)).seq
    (DescentTerminalProposalCheck.program w A.xCheck N A.x L.xWords)).seq
    (scan w A.y.base N (route L))).seq (DescentTerminalProposalCheck.program w A.yCheck N A.y L.ySlices)).seq
    (scan w A.keys slots (key L))

def m₁ (A : Layout) (L : Banks) (N : ℕ) (m : Memory w) := image A.x.base N (dense L) m
def m₂ (A : Layout) (L : Banks) (N : ℕ) (m : Memory w) :=
  DescentTerminalProposalCheck.after A.x L.xWords A.xCheck N (m₁ A L N m)
def m₃ (A : Layout) (L : Banks) (N : ℕ) (m : Memory w) := image A.y.base N (route L) (m₂ A L N m)
def m₄ (A : Layout) (L : Banks) (N : ℕ) (m : Memory w) :=
  DescentTerminalProposalCheck.after A.y L.ySlices A.yCheck N (m₃ A L N m)
def finalMem (A : Layout) (L : Banks) (N slots : ℕ) (m : Memory w) := image A.keys slots (key L) (m₄ A L N m)
def clocks (N slots : ℕ) := 172+322*N+64*slots

theorem exprMono {w a b : ℕ} (e : Expr) (ok : e.Fits w a) (h : a≤b) : e.Fits w b := by
  induction e with
  | row | lit=>trivial
  | lookup z _ ih=>exact ⟨bankMono ok.1 h,ih ok.2⟩
  | op _ _ _ l r=>exact ⟨l ok.1,r ok.2⟩
  | branch _ _ _ _ _ l r y n=>exact ⟨l ok.1,r ok.2.1,y ok.2.2.1,n ok.2.2.2⟩

private theorem seq_run (P Q : Procedure w) {src mid dst : Memory w} {p q : ℕ}
    (left : P.Exec src mid p ∧ CheapCode P) (right : Q.Exec mid dst q ∧ CheapCode Q) :
    (P.seq Q).Exec src dst (p+q) ∧ CheapCode (P.seq Q) :=
  ⟨@Procedure.Exec.then w P Q src mid dst p q left.1 right.1,
    @cheap_seq w P Q left.2 right.2⟩

theorem run (A : Layout) (L : Banks) (rm : Room A L w N slots) (m : Memory w) :
    (program A L w N slots).Exec m (finalMem A L N slots m) (clocks N slots) ∧ CheapCode (program A L w N slots) := by
  have limit : A.first+4*A.width+2+slots < 2^w := rm.last
  have reach : N ≤ A.width := rm.count
  have pos : 0 < A.width := Nat.two_pow_pos _
  have fx : A.x.Fits w A.xCheck :=
    ⟨pos, show A.width < 2^w by omega, le_rfl⟩
  have fy : A.y.Fits w A.yCheck :=
    ⟨pos, show A.width < 2^w by omega,
      show A.first+2*A.width+1+A.width ≤ A.first+3*A.width+1 by omega⟩
  have scanRun (out rows : ℕ) (expr : Expr) (mem : Memory w)
      (fit : expr.Fits w out) (room : out+rows < 2^w) :
      (scan w out rows expr).Exec mem (image out rows expr mem) (4+rows*(2*expr.work+4)) ∧
        CheapCode (scan w out rows expr) :=
    ⟨@scan_exec w out rows expr mem fit room, @scan_cheap w out rows expr⟩
  let xScan := scan w A.x.base N (dense L)
  let xCompare := DescentTerminalProposalCheck.program w A.xCheck N A.x L.xWords
  let yScan := scan w A.y.base N (route L)
  let yCompare := DescentTerminalProposalCheck.program w A.yCheck N A.y L.ySlices
  let keyScan := scan w A.keys slots (key L)
  have a := scanRun A.x.base N (dense L) m rm.inputDense
    (show A.first+N < 2^w by omega)
  have b := DescentTerminalProposalCheck.run A.x L.xWords (m₁ A L N m) fx
    (bankMono rm.x (show A.first ≤ A.first+A.width by omega)) rm.count rm.xCap
    (show A.first+A.width+(N+1) < 2^w by omega)
  have c := scanRun A.y.base N (route L) (m₂ A L N m)
    (exprMono _ rm.inputRoute (show A.first ≤ A.first+2*A.width+1 by omega))
    (show A.first+2*A.width+1+N < 2^w by omega)
  have d := DescentTerminalProposalCheck.run A.y L.ySlices (m₃ A L N m) fy
    (bankMono rm.y (show A.first ≤ A.first+3*A.width+1 by omega)) rm.count rm.yCap
    (show A.first+3*A.width+1+(N+1) < 2^w by omega)
  have e := scanRun A.keys slots (key L) (m₄ A L N m)
    (exprMono _ rm.inputKey (show A.first ≤ A.first+4*A.width+2 by omega)) rm.last
  have ab := seq_run xScan xCompare a b
  have abc := seq_run (xScan.seq xCompare) yScan ab c
  have abcd := seq_run ((xScan.seq xCompare).seq yScan) yCompare abc d
  have fee : 4+N*(2*(dense L).work+4)+(4+(N+1)*76)+(4+N*(2*(route L).work+4))+
      (4+(N+1)*76)+(4+slots*(2*(key L).work+4)) = clocks N slots := by
    change 4+N*(2*50+4)+(4+(N+1)*76)+(4+N*(2*31+4))+
      (4+(N+1)*76)+(4+slots*(2*30+4)) = 172+322*N+64*slots
    omega
  rw [← fee]
  exact seq_run (((xScan.seq xCompare).seq yScan).seq yCompare) keyScan abcd e

end
end Hierarchy.DescentTerminalChipRuntime

end OAI
