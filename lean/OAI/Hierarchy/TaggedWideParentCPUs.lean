import OAI.Hierarchy.TaggedWideMountedPair
import OAI.Hierarchy.TaggedWideHostAdmission
import OAI.Hierarchy.TaggedWideInstalledFloors

namespace OAI
/-! # Both real CPU gates and their shared binary input at every sufficiently large parent -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Tagged TaggedPrune
open WideControlJoin ThreeFlat.RAM PhysicalProcedure Filter WireTelescope
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A s : ℝ} (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (unitCost : ℕ)
variable (N : ℕ) (x : WideParent κ A)
local notation "d" => 2^v.W
local notation "W" => wordBits x.h d copies
local notation "g" => v.wideDated x.h x.w ell unitCost
local notation "l" => v.wideInstalledLayout x m ell short u δ ξ unitCost g
local notation "S" => v.wideInstalledSize x m ell unitCost g
local notation "highSeed" => v.wideInstalledHeader x m ell short u δ ξ unitCost g
  (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0)

structure ParentCPUs where
  ready : CountedReady v x.h x.w v.maxBits
  large : v.programRoomHeight≤x.h
  room : v.GateRoom x.h x.w v.maxBits l S
  first : Mounted x.h N
  paid : Mounted x.h N
  same : v.wideGates x.h x.w v.maxBits l S room=(first.gate,paid.gate)
  firstRows : first.rows≤N*2^x.h
  paidRows : paid.rows≤N*2^x.h
  scratch : S+2*2^x.h<2^W

variable {u}
theorem cofinal_parent_cpus (hu : TaggedWidthProfile.Admissible s u) :
    ∃N:ℕ,∀ᶠx : WideParent κ A in WideParent.large κ A,
      Nonempty (v.ParentCPUs m ell short u δ ξ unitCost N x) := by
  obtain ⟨N,hardware⟩:=v.cofinal_mounted_pair (κ:=κ) (A:=A) m ell short hu δ ξ unitCost
  obtain ⟨_,funded⟩:=v.cofinal_counted_ready (κ:=κ) (B:=A) v.maxBits
  have high : Tendsto (WideParent.h (κ:=κ) (A:=A)) (WideParent.large κ A) atTop:=tendsto_comap
  refine ⟨N,?_⟩
  filter_upwards [hardware,funded,high.eventually (eventually_ge_atTop v.programRoomHeight)] with x pair state tall
  obtain ⟨lim,first,paid,eqn,rows₀,rows₁,room⟩:=pair
  exact ⟨⟨state.1,tall,lim,first,paid,eqn,rows₀,rows₁,room⟩⟩

namespace ParentCPUs
variable {v m ell short δ ξ unitCost N x}
variable (cpu : v.ParentCPUs m ell short u δ ξ unitCost N x)
include cpu in
theorem age : v.wideStockHeight≤x.h :=
  (le_max_right v.wideSignedHeight v.wideStockHeight).trans cpu.ready.height

local notation "slot" => (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot
local notation "L" => (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.windows
local notation "es" => events v.mesh
variable (b : Fin k→ℕ)
local notation "G" => v.wideGates x.h x.w v.maxBits l S cpu.room
local notation "E" => OpenPins x.h x.w b
local notation "Z" => Fin (CalendarTape.bits slot es)
local notation "base" => v.wideFixedCPUInput x.h x.w S highSeed
local notation "label" => wideTagPin x.h x.w b

def header (e : E→Bool) (s : Z→Bool) := (L).tape es label base e s
def firstPins (i : (G).1.Head) : (E⊕Z)⊕Bool := (L).entryPin es label base i.1.val i.2
def paidPins (i : (G).2.Head) : (E⊕Z)⊕Bool := (L).entryPin es label base i.1.val i.2
def admitted (e : E→Bool) (s : Z→Bool) : Prop :=
  v.wideAdmitted x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le S highSeed e s

theorem reads (e : E→Bool) (s : Z→Bool) :
    headerRead (cpu.firstPins b) e s=(G).1.headBits (cpu.header b e s) ∧
    headerRead (cpu.paidPins b) e s=(G).2.headBits (cpu.header b e s) :=
  ⟨(L).read_header es label base e s,(L).read_header es label base e s⟩

set_option maxHeartbeats 1200000 in
theorem «prefix» (e : E→Bool) (s : Z→Bool) (auth : Function.Bijective (Tagged.tag (fun j=>e (.inl j)))) :
    (G).1.observed (cpu.header b e s) ((G).1.zeroFlag (F:=F) (0 : Fin 1))=if cpu.admitted b e s then 1 else 0 := by
  have bounds:=v.wide_installed_tape_bounds x m ell unitCost g
  exact v.widePrefixAccept x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le S highSeed l cpu.room
    cpu.ready bounds.2.2 (bounds.1.trans (bounds.2.1.trans bounds.2.2)) cpu.scratch rfl cpu.large e s auth

end ParentCPUs
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
