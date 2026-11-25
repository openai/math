import OAI.Hierarchy.TaggedWideInverseAccepted
import OAI.Hierarchy.TaggedWireActiveRouting

namespace OAI
/-! # Reading and admitting the original parent words and selector pins -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory AdaptiveProbe ProbeStage CoreBoard CoreRoute
open Tagged TaggedPrune Tagged.WideControlJoin WireTelescope StripChart CatalystArchive
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ) (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
local notation "D" => 2^v.W
local notation "W" => Native.wordBits h D Native.copies
local notation "P" => v.widePlacement h width
local notation "stock" => v.fixedTerminalStock P h width
local notation "es" => events v.mesh
local notation "L" => (v.wideSelector h width age budget small).format.windows
local notation "slot" => (v.wideSelector h width age budget small).format.slot
variable (S : ℕ) (seed : Boot.Tape h (2^v.W))
def wideOrigin (π : Equiv.Perm (Row h)) :=
  v.wideSignedMidAt h width S stock v.radius π.symm (wideRouteOrder h D k)
    (v.wideFundedRaw h width v.maxBits seed)

def wideTagPin (b : Fin k→ℕ) (i : Row h×Fin h) : OpenPins h width b :=
  .inl (portIndex h width (.inr (.inl i)))

variable {b : Fin k→ℕ}
local notation "E" => OpenPins h width b
local notation "origin" => v.wideOrigin h width S seed
local notation "base" => v.wideFixedCPUInput h width S seed
local notation "label" => wideTagPin h width b
local notation "Pin" => (E⊕Fin (CalendarTape.bits slot es))⊕Bool

def wideAdmitted (e : E→Bool) (word : Bits (CalendarTape.bits slot es)) : Prop :=
  ∃π : Equiv.Perm (Row h), (π : Row h→Row h)=Tagged.tag (fun j=>e (.inl j)) ∧
    ∃! a : CalendarTape.Path slot es (origin π),CalendarTape.encode slot es (origin π) a=word

local notation "adm" => v.wideAdmitted h width age budget small S seed
theorem wideAdmitted_iff {e : E→Bool} {word : Bits (CalendarTape.bits slot es)}
    (π : Equiv.Perm (Row h)) (matchTag : (π : Row h→Row h)=Tagged.tag (fun j=>e (.inl j))) :
    adm e word ↔ ∃! a : CalendarTape.Path slot es (origin π),CalendarTape.encode slot es (origin π) a=word := by
  constructor
  · rintro ⟨π',tag,witness⟩
    have same : π'=π:=Equiv.ext (fun i=>congrFun (tag.trans matchTag.symm) i)
    subst π'
    exact witness
  · exact fun ok=>⟨π,matchTag,ok⟩

variable {m : ℕ} (l : WideCPU.Layout m) (room : v.GateRoom h width v.maxBits l S)
local notation "G" => v.wideGates h width v.maxBits l S room

def widePrefixPins (i : G.1.Head) : Pin := (L).entryPin es label base i.1.val i.2
def widePaidPins (i : G.2.Head) : Pin := (L).entryPin es label base i.1.val i.2

theorem widePinReads (e : E→Bool) (word : Bits (CalendarTape.bits slot es)) :
    headerRead (v.widePrefixPins h width age budget small S seed l room) e word=
        G.1.headBits ((L).tape es label base e word) ∧
    headerRead (v.widePaidPins h width age budget small S seed l room) e word=
        G.2.headBits ((L).tape es label base e word) :=
  ⟨(L).read_header es label base e word,(L).read_header es label base e word⟩

theorem widePrefixAccept (ready : CountedReady v h width v.maxBits)
    (extent : v.wideFundedSize h width v.maxBits≤S) (low : 2^h≤S) (spare : S+2*2^h<2^W)
    (scratch : l.tagScratch=S) (large : v.programRoomHeight≤h)
    (e : E→Bool) (word : Bits (CalendarTape.bits slot es))
    (auth : Function.Bijective (Tagged.tag (fun j=>e (.inl j)))) :
    G.1.observed ((L).tape es label base e word) (G.1.zeroFlag (F:=F) (0 : Fin 1))=if adm e word then 1 else 0 := by
  let π:=Equiv.ofBijective (Tagged.tag (fun j=>e (.inl j))) auth
  have read:=v.wide_inverse_admission h width age budget small S seed label ready extent low spare e word π
    (fun _=>rfl) l scratch room large
  rw [v.wideAdmitted_iff h width age budget small S seed π rfl]
  exact read.2

theorem widePrefixLanguage {R : ℕ}
    (Z : PhysicalTerm.CalendarTerms F h D k width R v.radius 1 slot es origin)
    (Shared : Type) [Fintype Shared] (e : OpenPins h width (Z.nativeRouting Shared).catalyst→Bool)
    (word : Bits (CalendarTape.bits slot es)) (π : Equiv.Perm (Row h))
    (matchTag : (π : Row h→Row h)=Tagged.tag (fun j=>e (.inl j))) :
    adm e word ↔ ∃!i:Fin ((Z.nativeRouting Shared).count π),(Z.nativeRouting Shared).encoding π i=word :=
  (v.wideAdmitted_iff h width age budget small S seed π matchTag).trans (Z.encoding_iff Shared π word).symm

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
