import OAI.Hierarchy.TaggedWideBankPins
import OAI.Hierarchy.TaggedWideCalendarReceipt
import OAI.Hierarchy.TaggedWideControlDense
import OAI.Hierarchy.TaggedShorterScatter

namespace OAI
/-! # Reading the positive cuts from the paid controller and the public data aperture -/

noncomputable section
namespace Hierarchy.Tagged.WideStack
open ThreeFlat Routing Spill
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open TaggedShorterCompaction TaggedShorterNetwork TaggedShorterGroups WideControlJoin
open ProtocolStackContraction ProbeStage.CoreBoard.PhysicalTerm
open scoped Classical Fin.CommRing

/-- Index of the occupied, mask or ID word in the dense observation of the final state. -/
def frozenRow {C D U : ℕ} (base : ℕ) (room : base + (C+2*(C*2*D)) ≤ U)
    (field : TaggedShorterScatter.Field C D) : Fin U :=
  ⟨base+(TaggedShorterScatter.fieldIndex C D field).val,
    (Nat.add_lt_add_left (TaggedShorterScatter.fieldIndex C D field).isLt _).trans_le room⟩

variable {Ex Se P : Type} {gate : Gate}

/-- Candidates in the same supergroup and side share the public socket's data bits.
The three control fields use the literal row and bit emitted by the paid program. -/
def frozenReadPin (G : Type) [Fintype G] (D half modules n w base : ℕ)
    (room : base + (capacity G D half modules + 2*(capacity G D half modules*2*D)) ≤ gate.u)
    (bits : n≤gate.W) (data : Slot G D → Fin w → P) :
    Input (capacity G D half modules) D (n+w) → SitePins Ex Se P gate :=
  let ctrl := fun (f : TaggedShorterScatter.Field (capacity G D half modules) D)
      (j : Fin (gate.W+1)) =>
    (Sum.inr (Sum.inr (Sum.inr (frozenRow base room f,j))) : SitePins Ex Se P gate)
  bankPin (TaggedShorterGroups.read G D half modules)
    (fun i => ctrl (.inl i) 0) (fun sb i => ctrl (.inr (false,sb,i)) 0)
    (fun sb i j => ctrl (.inr (true,sb,i)) (j.castLE bits).castSucc)
    (fun q j => .inr (.inr (.inl (data q j))))

/-- At each format, the payload plane uses the original fixed group, side, port,
lane and bit. In particular, arbitrary inactive candidate rows have an address. -/
def calendarSlot {T G E H : Type} [Fintype H] {ports lanes dates view : ℕ}
    {width : T → ℕ} {privateCap : E → ℕ} {historyCap : H → ℕ} (t : T)
    (q : Slot G (ports*lanes)) (j : Fin (width t)) :
    DataWorkspace T G E H ports lanes dates view width privateCap historyCap :=
  .inl ⟨t,q,j⟩

variable {F : Type*} [Field F] (b : Board F) (base : ℕ)
set_option quotPrecheck false
local notation "C" => capacity b.Group b.D b.halfBatch b.modules
variable (room : base+(capacity b.Group b.D b.halfBatch b.modules+
    2*(capacity b.Group b.D b.halfBatch b.modules*2*b.D))≤gate.u) (bits : b.address≤gate.W)
    (data : Slot b.Group b.D→Fin b.width→P)

/-- This proof uses the numerical values actually stored at the three scatter fields.
The only read on the private assignment is the public shared-data socket. -/
theorem frozenReadPin_input (out : Memory gate.W) (one : 1<2^gate.W)
    (stored : ∀ f, out (gate.addr (frozenRow base room f)).val =
      (TaggedShorterScatter.contents (n:=b.address) b.counts b.bound b.positive (by have := b.batch; omega)
        b.place f : Word gate.W))
    {U : Type} (ord : U ≃ P) (ext : Ex→Bool) (sel : Se→Bool) (assignment : U→Bool)
    (payload : b.Slots) (read : ∀ q j, assignment (ord.symm (data q j))=payload q j) :
    CalendarTerms.readPins ord ext sel (gate.terminal out) assignment ∘
        frozenReadPin b.Group b.D b.halfBatch b.modules b.address b.width base room bits data =
      input (TaggedShorterGroups.read b.Group b.D b.halfBatch b.modules)
        payload b.settings.occupied b.settings.mask b.settings.id := by
  have width : b.halfBatch≤2^b.address := by have := b.batch; omega
  have full := width.trans (Nat.pow_le_pow_right (by decide : 0<2) bits)
  have val (f : TaggedShorterScatter.Field C b.D) :
      (out (gate.addr (frozenRow base room f)).val).val =
        TaggedShorterScatter.contents (n:=b.address) b.counts b.bound b.positive width b.place f := by
    rw [stored, Fin.val_cast_of_lt
      (TaggedShorterScatter.contents_fit b.counts b.bound b.positive width b.place f one full)]
  unfold frozenReadPin
  dsimp only
  apply bankPin_of_readbacks
  · exact read
  · intro i
    change (out (gate.addr (frozenRow base room (.inl i))).val).val.testBit 0=b.settings.occupied i
    rw [val]
    change (b.settings.occupied i).toNat.testBit 0=b.settings.occupied i
    cases b.settings.occupied i <;> decide
  · intro sb i
    change (out (gate.addr (frozenRow base room (.inr (false,sb,i)))).val).val.testBit 0=b.settings.mask sb i
    rw [val]
    change (b.settings.mask sb i).toNat.testBit 0=b.settings.mask sb i
    cases b.settings.mask sb i <;> decide
  · intro sb i j
    change (out (gate.addr (frozenRow base room (.inr (true,sb,i)))).val).val.testBit j.val=
      b.settings.id sb i j
    rw [val]
    change ((wordBits b.address).symm (b.settings.id sb i)).val.testBit j.val=b.settings.id sb i j
    rw [Computability.VPVNP.LiveHeader.testBit_wordBits,Equiv.apply_symm_apply]

/-- The terminal tensor of the paid near and far components is the installed
settings evaluation, including the summation over the internal compactor wires. -/
theorem frozenCut_closed [Fintype Ex] [Fintype Se] [Fintype P] (out : Memory gate.W)
    (one : 1<2^gate.W)
    (stored : ∀ f, out (gate.addr (frozenRow base room f)).val =
      (TaggedShorterScatter.contents (n:=b.address) b.counts b.bound b.positive (by have := b.batch; omega)
        b.place f : Word gate.W))
    {U : Type} (ord : U ≃ P) (ext : Ex→Bool) (sel : Se→Bool) (assignment : U→Bool)
    (payload : b.Slots) (read : ∀ q j,assignment (ord.symm (data q j))=payload q j) :
    (CutFormat.mk C b.D b.modules b.address b.width b.near b.far
      (frozenReadPin b.Group b.D b.halfBatch b.modules b.address b.width base room bits data)).closed
      (CalendarTerms.readPins ord ext sel (gate.terminal out) assignment) =
        b.settings.close payload := by
  exact congrArg (TaggedShorterBank.close (TaggedShorterBank.cut b.near b.far
    (lane F b.address b.address b.width)) (oracle F b.address b.width))
    (frozenReadPin_input b base room bits data out one stored ord ext sel assignment payload read)

namespace Leaf
variable {T E H J Tail : Type} [Fintype T] [Fintype E] [Fintype H] [Fintype J] [Fintype Tail]
    {N groups ports lanes w m : ℕ} {cls : T→ℕ} {records : T→Fin N→ProtocolRAMEmit.Row}
    (ins : ∀t, Installed F groups ports lanes w m (cls t) (records t)) (cap : E→ℕ)
    (tail : ((Bool × ((e:E) × Fin (cap e))) ⊕ (H ⊕ J)) ≃ Tail)
local notation "ord" => Equiv.sumCongr (Equiv.refl (Pos (banks ins))) tail
local notation "P" => Pos (banks ins) ⊕ Tail
variable (t : T)
local notation "bt" => (ins t).bank
local notation "C₀" => capacity (Fin groups) (ports*lanes) (ins t).half (ins t).modules

omit [Fintype E] [Fintype H] [Fintype J] in
/-- This is the cut equality at every summand of the calendar terminal. Reindexing
the private and chronological wires leaves the two public socket sides at their
literal addresses for all voltage, history and output assignments. -/
theorem frozen_cut_receipt [Fintype Ex] [Fintype Se] (base : ℕ)
    (room : base+(C₀+2*(C₀*2*(ports*lanes)))≤gate.u) (bits : (ins t).address≤gate.W)
    (out : Memory gate.W) (one : 1<2^gate.W)
    (stored : ∀f,out (gate.addr (frozenRow base room f)).val=
      (TaggedShorterScatter.contents (n:=(ins t).address) (bt).counts (bt).bound (bt).positive
        (by change (bt).halfBatch ≤ 2^(bt).address; have := (bt).batch; omega) (bt).place f:Word gate.W))
    (ext : Ex→Bool) (sel : Se→Bool)
    (z : ∀i,(banks ins i).Slots) (y : PrivatePorts cap) (h : H→Bool) (p : J→Bool) :
    (CutFormat.mk C₀ (ports*lanes) (ins t).modules (ins t).address (bt).width (ins t).near (ins t).far
      (frozenReadPin (Fin groups) (ports*lanes) (ins t).half (ins t).modules (ins t).address (bt).width
        base room bits (fun q j => (Sum.inl ⟨t,q,j⟩ : P)))).closed
        (CalendarTerms.readPins ord ext sel (gate.terminal out) (write (banks ins) cap z y h p)) =
      (bt).settings.close (z t) :=
  frozenCut_closed bt base room bits (fun q j => (Sum.inl ⟨t,q,j⟩ : P)) out one stored
    ord ext sel (write (banks ins) cap z y h p) (z t) (fun _ _ => rfl)

end Leaf

end Hierarchy.Tagged.WideStack

end
end OAI
