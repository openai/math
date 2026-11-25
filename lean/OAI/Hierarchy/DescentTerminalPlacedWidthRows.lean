import OAI.Hierarchy.DescentTerminalPlacedHeaderRoom
import OAI.Hierarchy.DescentTerminalNativeHeaderField
import OAI.Hierarchy.DescentTerminalExecUnique

namespace OAI
/-! # The two paid width tables through both terminal sparse scatters -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalEmitter DescentTerminalRowArena
open DescentKernelHistory DescentTerminalCableOrder DescentTerminalPorts DescentTerminalDenseGraphRead
open DescentTerminalGraphPositions DescentTerminalDenseWindow DescentTerminalDenseHeader DescentTerminalHeaderGroups
open Computability.BorderVNP.Crossing ThreeFlat.Routing
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {P : Type} [Fintype P] {d H p q w : ℕ} {bits : P→ℕ}
    (N : Network d P bits) (home : N.Site→Fin H) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
    (ext : P ↪ ℕ) (nodes : N.Site ↪ ℕ) (ops : ∀v,Boundary N v ↪ ℕ) (hp : 0<p) (hq : 0<q)
local notation "G_" => order N home native p ext nodes ops
local notation "ipt" => DescentTerminalHeaderGroups.stream (p:=p) N home native ext nodes ops q hp
local notation "ept" => DescentTerminalExteriorHeaders.stream (q:=q) (p:=p) N home native ext nodes ops

def CableRows (m : Memory w) (cable : DescentTerminalDenseHeaderRAM.Layout) : Prop :=
  ∀(t : ℕ) (_ : t<H*H) (live : 0<pairMass N home t),
    let g:=selected N home native ext nodes ops hp t live
    ∀k:Fin (poolBatchCount (Fintype.card (Order.At G_ g.site g.group)) q),
      let z:DescentTerminalDenseCableFetch.Packet N G_ q:=⟨g.site,g.other,g.group,g.near,k⟩
      m (cable.index.base+((ipt t).length+k.val))=(DescentTerminalDenseCableFetch.index N home native ext nodes ops z:Computability.VPVNP.BurstRAM.Word w) ∧
      m (cable.control.base+((ipt t).length+k.val))=((formatIndex q p
        (DescentTerminalDenseCableFetch.fmt N home native ext nodes ops (Nat.mul_pos hq hp) z)).val:Computability.VPVNP.BurstRAM.Word w)

def PublicRows (m : Memory w) (outer : DescentTerminalDenseHeaderRAM.Layout) : Prop :=
  ∀(i:Fin H) (g:Order.Group G_ i) (_:g.val=none) (k:Fin (poolBatchCount (Fintype.card (Order.At G_ i g)) q)),
    let len:=groupLengths N G_ i g
    let small:∀z,len z≤p:=fun z=>by dsimp [len,groupLengths];cases ((Order.inGroup G_ i g).symm z).val <;> exact Nat.min_le_left ..
    m (outer.index.base+((ept i.val).length+k.val))=((DescentTerminalDenseWindow.first len q
      (DescentTerminalPublicGroup.siteBase N home i) k.val/(q*p):ℕ):Computability.VPVNP.BurstRAM.Word w) ∧
    m (outer.control.base+((ept i.val).length+k.val))=((formatIndex q p (format len (Nat.mul_pos hq hp) small
      (DescentTerminalPublicGroup.siteBase N home i) k.val)).val:Computability.VPVNP.BurstRAM.Word w)

variable (cfg : DescentTerminalCompiledPrefix.Shape) (I : Input) (base : ℕ)
    (m : Memory w)
local notation "E_" => emitter cfg I base
local notation "s_" => cfg.terminal.plane
local notation "size_" => DescentTerminalDataPlane.Arena.size (s_).headerRows
local notation "head_" => DescentTerminalDataPlane.Arena.headerBase s_ (takeOff cfg I base)
local notation "second" => DescentTerminalDataPlane.Arena.second s_ (takeOff cfg I base)
local notation "inside" => (bodyPlane cfg I base).header
local notation "outside" => publicHeader cfg I base
local notation "beforeCable" => DescentTerminalDataPlane.file s_ (bodyPlane cfg I base) m
local notation "beforePublic" => DescentTerminalDataPlane.finalMem s_ (bodyPlane cfg I base) m
local notation "after_" fmt => if fmt then indexed cfg.terminal E_ m else external cfg.terminal E_ m

theorem field_rows (ready : DescentTerminalEmitter.Room cfg.terminal E_ w)
    (ci : (ipt (H*H)).length≤(s_).headerRows) (pu : (ept H).length≤(s_).headerRows)
    (cableReads : DescentTerminalDenseHeaderRAM.Reads inside
      (padded (n:=(s_).headerRows) (ipt (H*H))) beforeCable)
    (outerReads : DescentTerminalDenseHeaderRAM.Reads outside
      (padded (n:=(s_).headerRows) (ept H)) beforePublic)
    (fmt : Bool) :
    CableRows N home native ext nodes ops hp hq (after_ fmt) inside ∧
      PublicRows N home native ext nodes ops hp hq (after_ fmt) outside := by
  obtain ⟨cm,ec,_,cRows⟩:=native_headers_eof_fixed N home native ext nodes ops inside beforeCable
    hq hp (H*H) ci ready.plane.widths cableReads
  obtain ⟨em,ee,eRows⟩:=DescentTerminalExteriorHeaders.physical_headers N home native ext nodes ops
    outside beforePublic hq hp pu ready.ext outerReads
  have cEq : cm=beforePublic := ProtocolRAM.exec_unique _ _ _ _ ec
    (DescentTerminalDenseHeaderRAM.exec_any inside beforeCable ready.plane.widths).1
  have eEq : em=external cfg.terminal E_ m := ProtocolRAM.exec_unique _ _ _ _ ee
    (DescentTerminalDenseHeaderRAM.exec_any outside beforePublic ready.ext).1
  rw [cEq] at cRows
  rw [eEq] at eRows
  have endRow := DescentTerminalDataPlane.Arena.room (s_).headerRows
  have indexLow (x : ℕ) (bound : x<second+4*size_) :
      (after_ fmt) x=external cfg.terminal E_ m x := by
    cases fmt
    · rfl
    · apply Header.early _ _ ready.idx
      change x<second+4*size_+0*_
      omega
  have previous (x : ℕ) (bound : x<second) : (after_ fmt) x=beforePublic x := by
    have first:=indexLow x (by omega)
    exact first.trans (DescentTerminalDenseHeaderRAM.before_inputs _ _ ready.ext
      (by change x<second+0*size_;omega))
  constructor
  · intro t ht live
    dsimp only
    intro k
    obtain ⟨post,cut⟩:=stream_split N home native ext nodes ops hq hp t (H*H) ht live
    have kr : k.val<((selected N home native ext nodes ops hp t live).rows q).length := by
      simp [GroupBlock.rows]
    have lim : (ipt t).length+k.val < (s_).headerRows := by
      rw [cut,List.length_append,List.length_append] at ci
      omega
    obtain ⟨ix,ctl⟩:=cRows t ht live k
    exact ⟨(previous _ (by change head_+2*size_+_<head_+4*size_;omega)).trans ix,
      (previous _ (by change head_+3*size_+_<head_+4*size_;omega)).trans ctl⟩
  · intro i g hg k
    obtain ⟨post,cut⟩:=DescentTerminalExteriorHeaders.stream_append (q:=q) N home native ext nodes ops i g hg
    have kr : k.val<(DescentTerminalExteriorHeaders.block (q:=q) N home native ext nodes ops i g).length := by
      simp [DescentTerminalExteriorHeaders.block,chunkRows]
    have lim : (ept i.val).length+k.val < (s_).headerRows := by
      rw [cut,List.length_append,List.length_append] at pu
      omega
    obtain ⟨ix,ctl⟩:=eRows i g hg k
    exact ⟨(indexLow _ (by change second+2*size_+_<second+4*size_;omega)).trans ix,
      (indexLow _ (by change second+3*size_+_<second+4*size_;omega)).trans ctl⟩

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns

end OAI
