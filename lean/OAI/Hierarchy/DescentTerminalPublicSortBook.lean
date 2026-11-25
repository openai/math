import OAI.Hierarchy.DescentTerminalPublicIdentity
import OAI.Hierarchy.DescentTerminalMeterSuffix
import OAI.Hierarchy.DescentTerminalAddressPlan

namespace OAI
/-! # The inverse permutation in the actual resident suffix and its five public gather controls -/
namespace Hierarchy.DescentTerminalCompiledPrefix.Suffix
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalVertexFields Computability.BorderVNP.FragmentBucket
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {w blocks : ℕ} (S : Shape) (L : Layout) (F : MaskedShelf blocks)

theorem sorted_rows (m : Memory w) (room : Fits S L F w) (home : Fin S.packets → Fin S.sites)
    (src : ∀i,L.homes.read m (i.val:Word w)=((home i).val:Word w))
    (keep : ∀i : Fin S.packets,Frozen L (L.homes.base+(i.val:Word w).val%L.homes.size))
    (pagesLow : L.order.sorted+S.packets ≤ L.directory.texture.base)
    (eventsLow : L.order.sorted+S.packets ≤ L.emit.leaf.event.base) (i : Fin S.packets) :
    events S L F m (L.order.sorted+i.val)=(((dest home).symm i).val:Word w) := by
  have h : L.order.sorted+i.val < L.order.sorted+S.packets := Nat.add_lt_add_left i.isLt _
  have keys (u : Fin S.packets) : L.homes.read (positioned S L m) (u.val:Word w)=((home u).val:Word w) := by
    change positioned S L m _=_
    rw [positioned,DescentTerminalSiteOffsets.early _ _ _ (keep u).offsets,
      DescentTerminalRowPlan.before_publishing _ _ room.allocator (keep u).memories (keep u).books]
    exact src u
  rw [events,DescentTerminalEmitter.issued,DescentTerminalChipRuntime.image_low _ _ _ _ (h.trans_le eventsLow),
    pages,maskedMem,DescentTerminalChipRuntime.image_low _ _ _ _ (h.trans_le pagesLow),sockets,
    DescentTerminalPacketSlotRAM.retained _ _ _ _ _ (.inl (sorted_before S L i))]
  exact DescentTerminalExteriorPackets.sort_id _ _ _ _ _ S.sites_pos room.sort home keys i
end
end Hierarchy.DescentTerminalCompiledPrefix.Suffix

namespace Hierarchy.DescentTerminalPublicIdentity
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalPrimitiveArena DescentExteriorShelf
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section

/-- Only the first entry names mutable storage. Four lookups read the one fixed original table. -/
def controls (sortBase identityBase n : ℕ) (f : Fin 6) : Bank :=
  if f=0 then bank sortBase n else if f=3 ∨ f=5 then bank identityBase n else ⟨identityBase,0⟩

theorem flagged_before (j r t e origin : ℕ) {w : ℕ} (m : Memory w) {a : ℕ} (low : a < origin) :
    flaggedMem (j:=j) (r:=r) (t:=t) (e:=e) origin m a=m a := by
  have flag : a < flagOut (j:=j) (r:=r) (t:=t) (e:=e) origin := low.trans_le (Nat.le_add_right ..)
  have hp : a < start j r t e origin := low.trans_le (Nat.le_add_right ..)
  have key : a < keyAt j r t e origin := low.trans_le (Nat.le_add_right ..)
  rw [flaggedMem,DescentExteriorRejectWord.before _ _ _ flag]
  unfold serviceMemory DescentExteriorFetch.finalMem
  rw [DescentTerminalChipRuntime.image_low _ _ _ _ (by omega),
    DescentTerminalChipRuntime.image_low _ _ _ _ (by omega),
    DescentTerminalChipRuntime.image_low _ _ _ _ hp,
    DescentTerminalChipRuntime.image_low _ _ _ _ key]

theorem at_index {w} {m : Memory w} {addr n : ℕ} (live : n < 2^w) (i : Fin n) :
    (bank addr n).read m (i.val:Word w) = m (addr+i.val) := by
  have hi := i.isLt.trans_le (covered n)
  change m (addr+((i.val:Word w).val%(pad n)))=_
  rw [Fin.val_cast_of_lt (i.isLt.trans live),Nat.mod_eq_of_lt hi]

end
end Hierarchy.DescentTerminalPublicIdentity

namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open DescentTerminalPublicIdentity DescentTerminalPrimitiveArena
variable (S : Shape) (I : Input) (base identityAt : ℕ)
set_option quotPrecheck false
local notation "A" => rowArena S I base

/-- The immutable and stable-sort control columns all end before the physical flight. -/
theorem public_controls_earlier (early : identityAt+pad S.packets ≤ base) (i : Fin 6) :
    let c:=controls (A).order.sorted identityAt S.packets i
    c.base+c.size ≤ takeOff S I base := by
  intro c
  obtain ⟨toPages,toComp,_,_,_⟩ := stages S I base
  have upto:=(toPages.trans toComp)
  have span:=(A).stride_min
  change 2*S.sites+_+S.packets+1 < (A).stride at span
  have paid:=pad_le S.packets
  have sorted : (A).order.sorted+pad S.packets ≤ (A).finish := by
    change base+17*(A).stride+pad S.packets ≤ base+22*(A).stride
    omega
  have low := early.trans (((A).start_le 22).trans upto)
  have pos : 0 < pad S.packets := Nat.two_pow_pos _
  fin_cases i <;> first
    | exact sorted.trans upto
    | exact low
    | change identityAt+1 ≤ takeOff S I base;omega
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
