import OAI.Hierarchy.DescentTerminalChipReadback
import OAI.Hierarchy.DescentTerminalTransposePins
import OAI.Hierarchy.DescentTerminalScalarScanRead

namespace OAI
/-! # Unique shared proposals selected by the two real native mismatch flags -/
namespace Hierarchy.DescentTerminalChipRuntime
open DescentTerminalScalarTransposes DescentTerminalBinReaddress DescentTerminalDenseWindow
open DescentTerminalDenseWindowRAM DescentTerminalChipPins
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {K W q p w slots : ℕ}
local notation "d" => q*(W*p)
local notation "N" => K*W
local notation "c" => DescentTerminalBinFormat.controlBits W q
local notation "routes" => @DescentTerminalBinFormat.address W q

/-- Concrete dense addresses, clipped formats and true per-bin routes, padded
on the entire fixed terminal host before its hidden bits are chosen. -/
structure Content (K W q p : ℕ) where
  first : Fin (K*W)→ℕ
  format : Fin (K*W)→Format q (W*p)
  raw : ℕ→Word (q*(W*p))
  gate : Fin K→Tagged.Row (DescentTerminalBinFormat.controlBits W q)

def Content.rows (s : Content K W q p) (i : Fin N) :=
  DescentTerminalDenseWindow.word (s.format i) (s.raw (s.first i)) (s.raw (s.first i+1))

def Content.accepts (s : Content K W q p) (w : ℕ) (z : Inputs K W q p→Bool) :=
  rowWord (planes z false)=s.rows ∧
    DescentTerminalScalarTransposes.wide ∘ chunks (planes z true)=sliceOutput (bits:=w) routes s.gate (planes z false)

theorem Content.one (s : Content K W q p) (room : d≤w) : ∃!z,s.accepts w z := by
  obtain ⟨x,okX,onlyX⟩:=row_unique (K:=K) (W:=W) (q:=q) (piece:=p) s.rows
  obtain ⟨y,okY,onlyY⟩:=full_slice_unique (by simpa only [sliceWidth_eq] using room)
    routes s.gate x
  refine ⟨join x y,?_,?_⟩
  · simpa only [Content.accepts,(planes_join x y).1,(planes_join x y).2] using And.intro okX okY
  · intro z hz
    have hx:=onlyX (planes z false) hz.1
    have hy:=onlyY (planes z true) (hx ▸ hz.2)
    rw [←join_planes z,hx,hy]

def Content.witness (s : Content K W q p) (room : d≤w) := (s.one room).choose
theorem Content.valid_iff (s : Content K W q p) (room : d≤w) (z : Inputs K W q p→Bool) :
    s.accepts w z ↔ z=s.witness room := by
  refine ⟨fun v=>(s.one room).choose_spec.2 _ v,?_⟩
  rintro rfl
  exact (s.one room).choose_spec.1

/-- These are the literal materialized descriptor fields, unmodified dense
pool words, shared slice table and the two initial views of candidate bits. -/
structure Chips (A : Layout) (L : Banks) (s : Content K W q p) (m : Memory w)
    (z : Inputs K W q p→Bool) : Prop where
  denseFits : ∀b∈[L.index,L.formats,L.raw,L.menuStart,L.highField,L.denseROM],b.Fits w A.first
  sourceRoom : N≤L.index.size ∧ N≤L.formats.size ∧ Menus q (W*p)≤L.menuStart.size ∧
    radix q (W*p)≤L.highField.size ∧ Menus q (W*p)*(radix q (W*p)*radix q (W*p))≤L.denseROM.size
  rawRoom : ∀i,s.first i+1<L.raw.size
  source : DescentTerminalDenseWindowRAM.Inputs L.index L.formats L.raw L.menuStart L.highField L.denseROM
    s.first s.format s.raw m
  routeFits : L.gate.Fits w A.first ∧ L.joinedX.Fits w A.first ∧ L.pointer.Fits w A.first ∧ L.routeROM.Fits w A.first
  routeRoom : 3*N≤L.gate.size ∧ N≤L.joinedX.size ∧ 2^c≤L.pointer.size ∧ 2^c*2^(sliceWidth W q p)≤L.routeROM.size
  issuedGate : DescentTerminalBinSliceCheap.Inputs L.gate L.joinedX L.pointer L.routeROM routes s.gate (planes z false) m
  sourcePins : ∀i:Fin N,m (L.xWords.base+i.val)=DescentTerminalScalarTransposes.wide (rowWord (planes z false) i)
  routePins : ∀i:Fin N,m (L.ySlices.base+i.val)=DescentTerminalScalarTransposes.wide (chunks (planes z true) i)

theorem witnessed (A : Layout) (L : Banks) (s : Content K W q p) (rm : Room A L w N slots) (room : d≤w)
    (pos : 0<w) (m : Memory w) (z : Inputs K W q p→Bool) (physical : Chips A L s m z) :
    (finalMem A L N slots m (A.xCheck+N)=0 ∧ finalMem A L N slots m (A.yCheck+N)=0) ↔ z=s.witness room := by
  rw [flags A L rm m pos,←s.valid_iff room z]
  have x : ∀i:Fin N,(dense L).eval m (i.val:Word w)=DescentTerminalScalarTransposes.wide (s.rows i) := by
    intro i
    obtain ⟨ix,fmt,ptr,high,tab⟩:=physical.sourceRoom
    simpa only [dense,DescentTerminalScalarPadded.observed_at,Content.rows] using
      DescentTerminalScalarScanRead.dense_read L.index L.formats L.raw L.menuStart L.highField L.denseROM
        physical.denseFits ix fmt ptr high tab s.first physical.rawRoom s.format s.raw m physical.source room i
  have y : ∀i:Fin N,(route L).eval m (i.val:Word w)=sliceOutput routes s.gate (planes z false) i := by
    intro i
    obtain ⟨a,b,c₀,d₀⟩:=physical.routeFits
    obtain ⟨e,f,g,h⟩:=physical.routeRoom
    exact DescentTerminalScalarScanRead.route_read A.first L.gate L.joinedX L.pointer L.routeROM a b c₀ d₀
      e f g h routes s.gate _ m physical.issuedGate i
  constructor
  · rintro ⟨u,v⟩
    refine ⟨funext (fun i=>?_),funext (fun i=>?_)⟩
    · have h:=(physical.sourcePins i).symm.trans ((u i).symm.trans (x i))
      simpa only [low_wide] using congrArg (low room) h
    · exact (physical.routePins i).symm.trans ((v i).symm.trans (y i))
  · rintro ⟨u,v⟩
    exact ⟨fun i=>(x i).trans ((congrArg (DescentTerminalScalarTransposes.wide (bits:=w)) (congrFun u i).symm).trans
      (physical.sourcePins i).symm),fun i=>(y i).trans ((congrFun v i).symm.trans (physical.routePins i).symm)⟩

end
end Hierarchy.DescentTerminalChipRuntime

end OAI
