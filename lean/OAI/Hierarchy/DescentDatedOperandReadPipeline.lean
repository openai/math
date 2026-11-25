import OAI.Hierarchy.DescentOperandReadShape
import OAI.Hierarchy.DescentDatedOperandCoordinateBooks
import OAI.Hierarchy.DescentDatedOperandSelectionRun
import OAI.Hierarchy.DescentDatedTicketOccurrence

namespace OAI
/-! # The causal sequence of reads before the eight ordinary ticket columns -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentSIMDLookup DescentPackedZip DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable (g : Geometry)
local notation "J" => g.jobs
local notation "P" => g.paths
local notation "B" => g.blocks
local notation "D" => g.degree
local notation "C" => g.cap
local notation "a" => g.digitBits
local notation "b" => g.resultBits
local notation "M" => g.lanes
local notation "O" => B*(C*11)
local notation "S₁" => P*(B*(D*C))
local notation "S₂" => P*(D+1)
local notation "S₃" => P*(B*(C*3))
local notation "S₄" => P*O

/-- Every input is a physical RAM row expression. The four many-candidate
fields enumerate public old coordinates independently of the contents of W. -/
structure Sources (g : Geometry) where
  origin : Fin g.jobs → Fin 6 → Expr
  prior : Fin g.jobs → Fin 4 → Expr
  mouth : Fin g.jobs → Fin 3 → Expr
  old : Fin g.jobs → Fin 4 → Fin (g.paths*(g.blocks*(g.degree*g.cap))) → Expr
  path : Fin (g.paths*(g.degree+1)) → Expr
  anchor : Fin g.jobs → Fin 5 → Fin (g.paths*(g.blocks*(g.cap*3))) → Expr
  raw : Fin g.jobs → Fin 8 → Fin (g.paths*(g.blocks*(g.cap*11))) → Expr
  rank : Fin g.paths → Expr

variable (s : Sources g)
def layout (cols count : ℕ) : DescentDatedOperandMux.Layout :=
  ⟨g.hosts,g.groups,M,J*cols,count,keyWidth count,a⟩
def lookup (arity cols count base : ℕ) (j : Fin J) (f : Fin cols) : Expr :=
  .lookup (DescentDatedOperandSelectionRun.bank (layout g cols count) 1 arity a base (finProdFinEquiv (j,f))) .row
def after (arity cols count base : ℕ) :=
  DescentDatedOperandSelectionRun.endAddress (layout g cols count) 1 arity a base

def readStage {cols count n : ℕ} (law : Fin 1 → (Fin n → Cell a) → Cell (keyWidth count))
    (args : Fin J → Fin n → Expr) (head : Fin J → Fin cols → Fin count → Expr) (base w : ℕ) :=
  DescentDatedOperandSelectionRun.phase (layout g cols count) law (fun _=>0)
    (fun p=>args (finProdFinEquiv.symm p).1)
    (fun p=>head (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) base w

def oldArgs (j : Fin J) : Fin 6 → Expr :=
  ![s.origin j 0,s.prior j 0,s.origin j 1,s.origin j 2,s.prior j 1,s.prior j 2]
def oldPhase :=readStage g (oldLaw P B D C a) (oldArgs g s) s.old
def old (base : ℕ) := lookup g 6 4 S₁ base
def pathBase (base : ℕ) := after g 6 4 S₁ base

def pathArgs (base : ℕ) (j : Fin J) : Fin 5 → Expr :=
  ![s.origin j 0,s.origin j 1,old g base j 3,old g base j 1,old g base j 2]
def pathPhase (base w : ℕ) :=readStage (cols:=1) g (pathLaw P D a) (pathArgs g s base) (fun _ _=>s.path) (pathBase g base) w
def path (base : ℕ) (j : Fin J) := lookup g 5 1 S₂ (pathBase g base) j 0
def anchorBase (base : ℕ) := after g 5 1 S₂ (pathBase g base)

def anchorArgs (base : ℕ) (j : Fin J) : Fin 9 → Expr :=
  ![s.origin j 0,s.prior j 0,s.origin j 1,path g base j,s.origin j 2,old g base j 3,old g base j 2,s.origin j 4,s.mouth j 0]
def anchorPhase (base w : ℕ) := readStage g (anchorLaw P B C a) (anchorArgs g s base) s.anchor (anchorBase g base) w
def anchor (base : ℕ) :=lookup g 9 5 S₃ (anchorBase g base)
def rawBase (base : ℕ) :=after g 9 5 S₃ (anchorBase g base)

def rawArgs (base : ℕ) (j : Fin J) : Fin 5 → Expr :=
  ![s.origin j 0,s.origin j 1,path g base j,anchor g base j 4,s.mouth j 1]
def rawPhase (base w : ℕ) :=readStage g (rawLaw P O a) (rawArgs g s base) s.raw (rawBase g base) w
def raw (base : ℕ) :=lookup g 5 8 S₄ (rawBase g base)
def rankBase (base : ℕ) :=after g 5 8 S₄ (rawBase g base)

def rankArgs (j : Fin J) : Fin 3 → Expr := ![s.origin j 0,s.prior j 0,s.origin j 1]
def rankPhase (base w : ℕ) :=readStage (cols:=1) g (localLaw P a) (rankArgs g s) (fun _ _=>s.rank) (rankBase g base) w
def rank (base : ℕ) (j : Fin J) :=lookup g 3 1 P (rankBase g base) j 0
def finalBase (base : ℕ) :=after g 3 1 P (rankBase g base)

/-- The terminal table uses the original carrier of all provided arguments.
Positions 6 and 7 of the raw family are the earned serial and peer of the
same parent's successor cable. -/
def finalArgs (base : ℕ) (j : Fin J) : Fin 17 → Expr :=
  ![s.origin j 0,s.prior j 0,rank g base j,s.origin j 2,s.origin j 1,path g base j,
    raw g base j 6,raw g base j 7,s.mouth j 1,anchor g base j 0,anchor g base j 1,anchor g base j 2,anchor g base j 4,
    raw g base j 2,raw g base j 3,raw g base j 4,raw g base j 5]
def finalLaw (f : Fin 8) (x : Fin 17 → Cell a) : Cell b :=
  let t:=fun i=>(x i).val
  let accepted:=(DescentDatedOperandCoordinates.digit S₄ (rawSocket P O (t 0) (sourcePath (t 0) (t 4) (t 5)) (t 12) (t 8))).val
  ((Ticket.fields B (t 0) (t 1) (t 2) (t 3) accepted (t 6) (t 7) (t 8)
    ![t 9,t 10,t 11,0,t 12] ![0,0,t 13,t 14,t 15,t 16] f:ℕ):Cell b)

theorem final_dead (f : Fin 8) : finalLaw g f (fun _=>0)=0 := by simp [finalLaw,Ticket.fields]

def endAddress (base : ℕ) :=DescentOperandFamilyBook.endAddress 8 17 a M (finalBase g base)
def bankPhase (base w : ℕ) : NativePhase w :=
  ⟨DescentOperandFamilyBook.program (finalLaw g) M (finalBase g base) w,
    DescentOperandFamilyBook.ticks 8 17 a M,DescentOperandFamilyBook.image (finalLaw g) M (finalBase g base),
    @DescentStaticWordColumn.cheap _ _ _ _⟩
def phase (base w : ℕ) :=
  (((((oldPhase g s base w).seq (pathPhase g s base w)).seq (anchorPhase g s base w)).seq
    (rawPhase g s base w)).seq (rankPhase g s base w)).seq (bankPhase g base w)
def expression (base : ℕ) (j : Fin J) (f : Fin 8) :=
  DescentOperandFamilyBook.expr (finalLaw g) M (finalBase g base) f (finalArgs g s base j)

theorem source_work (base : ℕ) (j : Fin J) (f : Fin 8) (maxWork : ℕ)
    (early : ∀i,(finalArgs g s base j i).work ≤ maxWork) :
    (expression g s base j f).work≤14+17*(maxWork+11) :=
  DescentOperandFamilyBook.expr_work (finalLaw g) M (finalBase g base) f _ maxWork early

theorem footprint (base : ℕ) : endAddress g base=base+endAddress g 0 :=by
  simp only [endAddress,finalBase,rankBase,rawBase,anchorBase,pathBase,after,DescentDatedOperandSelectionRun.endAddress,
    DescentDatedOperandSelectionRun.nextAddress,DescentDatedOperandMux.endAddress,DescentDatedOperandMux.start,
    DescentOperandFamilyBook.endAddress,Nat.zero_add,Nat.add_assoc]

end
end Hierarchy.DescentDatedOperandReadPipeline

end OAI
