import OAI.Hierarchy.DescentResetScalarChart
import OAI.Hierarchy.DescentResetStencilComputed
import OAI.Hierarchy.DescentResetDatedSplits
import OAI.Hierarchy.DescentResetChannelSubwords

namespace OAI
/-! # Every address after the old GL word bank has been split to the selected lane size -/
namespace Hierarchy.DescentPlainTerminal.Suffix
open DescentSIMDLookup DescentPackedColony DescentPacking.PackedMatch.Local
open ProtocolRAM
noncomputable section

/-- Public degrees and sizes of a fixed reset epoch. Each selected basis uses the same layout. -/
structure StencilBook where
  hosts : ℕ
  c : ℕ
  m : ℕ
  degree : ℕ
  maxPorts : ℕ
  high : ℕ
  M : ℕ
  b : ℕ
  n : ℕ
  t : ℕ
  levels : ℕ
  total : ℕ

namespace StencilBook
variable (S : StencilBook)
def r := S.m-S.c
def rows := S.hosts*chunks (2^S.c) S.M
def splitBits := Frame.pageBits S.hosts (2^S.c) S.r S.b S.M
def start (base : ℕ) := base+2^(Nat.clog 2 S.rows)
def split (base : ℕ) (roster weight : Bank) : Frame.Chart:=⟨S.start base,S.splitBits,roster,weight⟩
def afterSplit (base : ℕ) := S.start base+(S.degree+4+5*S.r)*2^S.splitBits
def header (base : ℕ) : PortLevels.AddressBook:=⟨S.afterSplit base,S.hosts,2^S.c,S.M,S.m,S.high,S.maxPorts⟩
def narrow (base : ℕ) : Bank := ⟨Cutoff.finish (S.header base).stop S.levels S.total,S.b*2^S.r*S.M⟩
def afterHeader (base : ℕ) := (S.narrow base).base+(S.narrow base).size
def readers (base : ℕ) : Stencil.ReaderTables.Chart:=⟨S.afterHeader base,S.hosts,S.c,S.m,S.n,S.b,S.M⟩
def last (base : ℕ) := Stencil.lastChart (S.readers base) (S.degree+S.degree) S.t
def output (base : ℕ) := (S.last base).out
def endAddress (base : ℕ) := (S.last base).endAddress

theorem split_end (base : ℕ) (roster weight : Bank) :
    (S.split base roster weight).fresh S.degree S.r+(S.r+1)*(S.split base roster weight).page=(S.header base).origin := by
  change S.start base+(S.degree+3+4*S.r)*2^S.splitBits+(S.r+1)*2^S.splitBits=S.start base+(S.degree+4+5*S.r)*2^S.splitBits
  ring

theorem output_end (base : ℕ) : S.endAddress base=S.output base+S.rows:=rfl

theorem extent (base : ℕ) :
    let a:=S.n*Stencil.count S.r (S.degree+S.degree)
    let e:=Stencil.ReaderTables.largest S.r S.m S.n S.b S.M
    let rowsPage:=2^(Nat.clog 2 S.rows)
    let hostPage:=2^(Nat.clog 2 S.hosts)
    S.endAddress base=base+rowsPage+
      (S.degree+4+5*S.r)*2^S.splitBits+
      (rowsPage+2*hostPage+2^S.levels+2^(S.levels+S.total)+2^(S.b*2^S.r*S.M))+
      (rowsPage+Fintype.card (Stencil.ReaderTables.Key S.r)*2^e+
        (S.m+1)*2^((2^S.r*S.m+2^S.r)*S.M))+
      ((Stencil.count S.r (S.degree+S.degree)+1)*2^((a+S.n)*S.M)+2^(a*S.M)+2*rowsPage+S.rows) := by
  dsimp [endAddress,output,last,Stencil.lastChart,readers,afterHeader,narrow,header,afterSplit,start,
    Stencil.Layout.Chart.endAddress,Stencil.Layout.Chart.out,Stencil.Layout.Chart.scratch,
    Stencil.Layout.Chart.mask,Stencil.Layout.Chart.table,Stencil.Layout.Chart.rowRoom,
    Stencil.Layout.Chart.bits,Stencil.Layout.Chart.rows,Stencil.Layout.Chart.a,Stencil.Layout.Chart.N,
    Stencil.ReaderTables.Chart.stop,Stencil.ReaderTables.Chart.planeBase,Stencil.ReaderTables.Chart.first,
    Stencil.ReaderTables.Chart.mask,Stencil.ReaderTables.Chart.page,Stencil.ReaderTables.Chart.rows,
    Stencil.ReaderTables.Chart.r,StencilTables.start,Cutoff.finish,
    PortLevels.AddressBook.stop,PortLevels.AddressBook.lead,PortLevels.AddressBook.depth,PortLevels.AddressBook.pos,
    PortLevels.AddressBook.hbits,PortLevels.AddressBook.rbits,PortLevels.AddressBook.rows,Bank.size,r,rows]
  ring_nf
  ac_rfl

theorem translated (base ceil : ℕ) : S.endAddress (base+ceil)=S.endAddress base+ceil := by
  rw [S.extent (base+ceil),S.extent base]
  omega

theorem socket_count : Fintype.card (Stencil.ReaderTables.Key S.r)=1+(2^S.r+S.r*2^S.r)+(2^S.r)^2 := by
  simp [Stencil.ReaderTables.Key,DescentColonies.Block,pow_two,Nat.add_assoc]

theorem output_before (base : ℕ) (p : DescentSIMDLookup.Row S.hosts (2^S.c) S.M) :
    S.output base+(DescentSIMDLookup.row S.hosts (2^S.c) S.M p).val<S.endAddress base:=by
  rw [S.output_end];exact Nat.add_lt_add_left (DescentSIMDLookup.row _ _ _ p).isLt _

end StencilBook
end
end Hierarchy.DescentPlainTerminal.Suffix

end OAI
