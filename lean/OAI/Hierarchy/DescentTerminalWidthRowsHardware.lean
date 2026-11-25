import OAI.Hierarchy.DescentTerminalWidthRowLast
import OAI.Hierarchy.DescentTerminalHeaderScatter
import OAI.Hierarchy.DescentTerminalPrimitiveSpace
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.ProtocolRAMGeneratedWriteCheap

namespace OAI
/-! # Native storage and instruction counts for grouped terminal width rows -/
namespace Hierarchy.DescentTerminalWidthRowsRAM
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalPrimitiveArena
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ThreeFlat.Routing
open DescentStaticWordColumn (names names_scan names_seq names_mount)
noncomputable section

structure Layout where
  origin : ℕ
  groups : ℕ
  rows : ℕ
  cap : ℕ
  source : Bank

namespace Layout
variable (L : Layout)

def ceil : Bank := ⟨L.origin, Nat.clog 2 (L.cap+1)⟩
def last : Bank := ⟨L.origin+L.ceil.size, Nat.clog 2 (L.cap+1)⟩
def entries := 2*L.ceil.size
def «prefix» : Bank := ⟨L.origin+L.entries, Nat.clog 2 L.groups⟩
def output : Bank := ⟨L.prefix.base+L.prefix.size, Nat.clog 2 L.rows⟩
def sink := L.output.base+L.output.size
def addresses := L.sink+1
def words := L.addresses+L.groups
def stop := L.words+L.groups

def literal (q p i : ℕ) := if i<L.ceil.size then poolBatchCount i q else tailCode q p (i-L.ceil.size)
def rank : Expr := .lookup L.ceil (.lookup L.source .row)
def total : Expr := if L.groups=0 then .lit 0 else .lookup L.prefix (.lit (L.groups-1))
def fill (q p : ℕ) : Expr := .branch .lt .row L.total (.lit (full q p)) (.lit (blank q p))
def rawDest : Expr := .op .sub (.op .add (.lit L.output.base) (.lookup L.prefix .row)) (.lit 1)
def dest : Expr := .branch .eq L.rank (.lit 0) (.lit L.sink)
  (DescentTerminalHeaderScatter.bounded L.output L.rawDest)
def datum : Expr := .lookup L.last (.lookup L.source .row)

def program (q p w : ℕ) : Procedure w :=
  (((DescentStaticWordColumn.program w L.origin (L.literal q p) L.entries).seq
    (DescentTerminalHeaderPrefixRAM.program w L.prefix.base L.groups .add L.rank)).seq
    (scan w L.output.base L.rows (L.fill q p))).seq
    (ProtocolRAMGeneratedWrite.program w L.addresses L.words L.groups L.dest L.datum)

def clocks (q p : ℕ) :=
  (((4+10*L.entries)+(4+L.groups*(2*DescentTerminalHeaderPrefixRAM.work .add L.rank+4)))+
    (4+L.rows*(2*(L.fill q p).work+4)))+ProtocolRAMGeneratedWrite.work L.groups L.dest L.datum

theorem cheap (q p w : ℕ) : CheapCode (L.program q p w) :=
  @cheap_seq w _ _
    (@cheap_seq w _ _
      (@cheap_seq w _ _
        (@DescentStaticWordColumn.cheap w L.origin (L.literal q p) L.entries)
        (@DescentTerminalHeaderPrefixRAM.cheap w L.prefix.base L.groups .add L.rank))
      (@scan_cheap w L.output.base L.rows (L.fill q p)))
    (@ProtocolRAMRankCheap.generated w L.addresses L.words L.groups L.dest L.datum)

theorem stop_eq : L.stop=L.origin+L.entries+pad L.groups+pad L.rows+1+2*L.groups := by
  change ((L.origin+L.entries+pad L.groups+pad L.rows+1)+L.groups)+L.groups=_
  omega

theorem entries_le : L.entries ≤ 4*L.cap+6 := by
  have h:=pad_le (L.cap+1)
  change 2*pad (L.cap+1)≤_
  omega

theorem rank_work : L.rank.work=12 := rfl
theorem dest_work : L.dest.work=32 := rfl
theorem datum_work : L.datum.work=12 := rfl
theorem fill_work (q p : ℕ) : (L.fill q p).work=if L.groups=0 then 6 else 11 := by
  by_cases h:L.groups=0 <;> simp only [fill,total,h,ite_eq_left,ite_false,Expr.work]

private theorem prefix_names (w : ℕ) :
    names (DescentTerminalHeaderPrefixRAM.program w L.prefix.base L.groups .add L.rank)=87 := by
  simp only [names,DescentTerminalHeaderPrefixRAM.program,PhysicalInputPhases.writing,Term.labels_eq,
    DescentTerminalHeaderPrefixRAM.binds,DescentTerminalHeaderPrefixRAM.work,rank_work]

private theorem generated_names (w : ℕ) :
    names (ProtocolRAMGeneratedWrite.program w L.addresses L.words L.groups L.dest L.datum)=218 := by
  simp only [ProtocolRAMGeneratedWrite.program,names_seq,names_scan,dest_work,datum_work]; rfl

theorem names_exact (q p w : ℕ) :
    names (L.program q p w)=15*(L.entries+1)+(if L.groups=0 then 340 else 360) := by
  simp only [program,names_seq,names_mount,prefix_names,names_scan,generated_names,fill_work]
  split <;> omega

theorem clocks_exact (q p : ℕ) :
    L.clocks q p=23+10*L.entries+148*L.groups+L.rows*(if L.groups=0 then 16 else 26) := by
  simp only [clocks,DescentTerminalHeaderPrefixRAM.work,rank_work,ProtocolRAMGeneratedWrite.work,
    dest_work,datum_work,fill_work]
  split <;> ring

/-- Bounds for all four rounded bank views and the particular expressions consuming them. -/
structure Fits (q p w : ℕ) : Prop where
  ceil : L.ceil.Fits w L.prefix.base
  last : L.last.Fits w L.prefix.base
  «prefix» : L.prefix.Fits w L.output.base
  output : L.output.Fits w L.addresses
  rank : L.rank.Fits w L.prefix.base
  fill : (L.fill q p).Fits w L.output.base
  dest : L.dest.Fits w L.addresses
  datum : L.datum.Fits w L.addresses
  installEnd : L.origin+L.entries<2^w
  prefixEnd : L.prefix.base+L.groups<2^w
  outputEnd : L.output.base+L.rows<2^w
  columns : L.addresses+L.groups≤L.words
  limit : L.words+L.groups<2^w

theorem fits (q p w : ℕ) (source : L.source.Fits w L.origin) (room : L.stop<2^w) :
    L.Fits q p w := by
  have b0 : L.origin ≤ L.prefix.base := Nat.le_add_right ..
  have b1 : L.prefix.base ≤ L.output.base := Nat.le_add_right ..
  have b2 : L.output.base ≤ L.addresses := by change _≤L.output.base+L.output.size+1; omega
  have b3 : L.addresses ≤ L.stop := by change _≤L.addresses+L.groups+L.groups; omega
  have hold (b : Bank) {top : ℕ} (inside : b.base+b.size≤top) (before : top≤L.stop) :
      b.Fits w top :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt ((inside.trans before).trans_lt room),inside⟩
  have up {b : Bank} {x y : ℕ} (fit : b.Fits w x) (le_ : x≤y) : b.Fits w y :=
    ⟨fit.1,fit.2.1,fit.2.2.trans le_⟩
  have past := b1.trans (b2.trans b3)
  have cb : L.ceil.Fits w L.prefix.base := hold _ (by
    change L.origin+L.ceil.size≤L.origin+2*L.ceil.size;omega) past
  have lb : L.last.Fits w L.prefix.base := hold _ (by
    change L.origin+L.ceil.size+L.ceil.size≤L.origin+2*L.ceil.size;omega) past
  have pb : L.prefix.Fits w L.output.base := hold _ le_rfl (b2.trans b3)
  have ob : L.output.Fits w L.addresses := hold _ (Nat.le_succ _) b3
  have rk : L.rank.Fits w L.prefix.base := ⟨cb,up source b0,trivial⟩
  have later := b1.trans b2
  have cur : L.prefix.Fits w L.addresses := up pb b2
  have raw : L.rawDest.Fits w L.addresses := ⟨⟨trivial,cur,trivial⟩,trivial⟩
  have bounded_ : (DescentTerminalHeaderScatter.bounded L.output L.rawDest).Fits w L.addresses :=
    ⟨trivial,⟨raw,trivial⟩,trivial⟩
  have dest_ : L.dest.Fits w L.addresses :=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ later rk,trivial,trivial,bounded_⟩
  have data_ : L.datum.Fits w L.addresses := ⟨up lb later,up source (b0.trans later),trivial⟩
  have all_ : L.total.Fits w L.output.base := by
    unfold total
    split
    · trivial
    · exact ⟨pb,trivial⟩
  have hd : L.groups≤L.prefix.size := covered _
  have ht : L.rows≤L.output.size := covered _
  exact ⟨cb,lb,pb,ob,rk,⟨trivial,all_,trivial,trivial⟩,dest_,data_,past.trans_lt room,
    (Nat.add_le_add_left hd _).trans_lt ((b2.trans b3).trans_lt room),
    (Nat.add_le_add_left ht _).trans_lt ((Nat.le_succ L.sink).trans_lt (b3.trans_lt room)),
    le_rfl,room⟩

end Layout
end
end Hierarchy.DescentTerminalWidthRowsRAM

end OAI
