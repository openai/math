import OAI.Hierarchy.DescentTerminalPurchasedSockets
import OAI.Hierarchy.DescentTerminalMaskReady
import OAI.Hierarchy.DescentTerminalNormalizedVenues

namespace OAI
/-! # Original occupancy and installed lookup tables at the branch socket date -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalVertexFields DescentTerminalSiteShelves
open DescentTerminalPrimitiveFrames DescentTerminalEmitter.Compact DescentSixParty DescentCompiler
open DescentTerminalGraphPositions DescentSIMDLookup
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {blocks V₀ B w : ℕ} (V : Home.Format) (S : Shape) (I : Input) (R : MaskAllocation.Channels blocks)
variable (start header : ℕ) (short : V₀*span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
variable (literal : Literals I.sources)
local notation "cpu" => meter V R start
local notation "ba" => afterMeter V S R start
local notation "regs" => registers V S R start header
local notation "abi" => layout S I ba regs
local notation "arena" => rowArena S I ba
local notation "num" => channelSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords)
  (N:=V.nodes) (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)
local notation "cap" => cohortSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords)
  (N:=V.nodes) (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=blocks)
local notation "incoming" => input V S I R start header short literal
local notation "socketsAt" => fun m : Memory w => Suffix.sockets S abi ((arena).mount (incoming m))

/-- The literal shift and menu pages installed for the counter remain available
at the actual socket pass, after the physical row arena was mounted. -/
theorem sockets_mask (m : Memory w) (prior : ∀ f,(R.bank f).base+(R.bank f).size≤ start)
    (headerLow : header<start) (old : Earlier S I ba (cpu).layout w) (room : last V S I R start<2^w) :
    MountedMask (groups:=V.groups) (cpu).layout (socketsAt m) short := by
  have floor : ba < 2^w := by
    obtain ⟨a,b,c,d,e⟩ := stages S I ba
    exact ((arena).start_le 22).trans_lt (a.trans_lt (b.trans_lt (c.trans_lt (d.trans_lt (e.trans_lt room)))))
  have geometry := MaskAllocation.prepared (sites:=S.sites) R start header
    (loaded (pageEnd S I ba) I.sources literal m) short prior headerLow floor
  have preset : MountedMask (groups:=V.groups) (cpu).layout (incoming m) short := geometry.2.2.1
  have cut : (cpu).base ≤ ba := by change _ ≤ (cpu).base+_+_+_+3; omega
  have keep (x : ℕ) (hx : x<ba) : socketsAt m x = incoming m x :=
    sockets_prior S I ba regs (cpu).layout _ (suffix_room S I ba (cpu).layout regs old room) hx
  have held (b : Bank) (end_ : b.base+b.size ≤ (cpu).base) (x : Word w) :
      b.read (socketsAt m) x = b.read (incoming m) x :=
    bank_below (incoming m) (socketsAt m) b ba (end_.trans cut) keep x
  have tableLow : (cpu).layout.table.base+(cpu).layout.table.size ≤ (cpu).base := by
    have cardinal : 2^(∑f : Fin (channels blocks),num f)=cap := by
      symm; unfold cohortSize; rw [Finset.prod_pow_eq_pow_sum]
    change start+MaskAllocation.marks num+2^(∑f : Fin (channels blocks),num f) ≤ start+(MaskAllocation.marks num+cap)
    rw [cardinal]
    omega
  exact ⟨fun f z => (held _ (geometry.1.old f).2.2.2 z).trans (preset.shift f z),
    fun j => (held _ tableLow (j.val:Word w)).trans (preset.menu j)⟩

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
