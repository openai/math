import OAI.Computability.BorderVNP.TransmissionSiteAdvice

/-! # The advised reference index in the literal packet of §11 -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM RoutingISA RoutingISA.Pins
open private wordData_length from OAI.Computability.BorderVNP.TeamTapeHandoffFrame

/-- The three consecutive parts of the physical advice packet. The frame extension
has one word for each field from 31 through 111 inclusive. -/
structure ReferencePacket (w d : ℕ) where
  /-- Header, gates and input addresses of the signed residue-entry routine. -/
  entry : List (Word w)
  /-- The 81 scalar words installed after the fixed boot frame. -/
  extension : Fin 81 → Word w
  /-- The chosen matrix-index coordinate H*. -/
  reference : Fin d → Bool

variable {w d : ℕ}

/-- Number of packed bits preceding the reference index. -/
def ReferencePacket.offset (p : ReferencePacket w d) : ℕ := w * (p.entry.length+81)

/-- The entry data and extension words precede the unmodified reference-index bits. -/
def ReferencePacket.bits (p : ReferencePacket w d) : List Bool :=
  (p.entry ++ List.ofFn p.extension).flatMap wordBits ++ List.ofFn p.reference

private theorem packetPrefix_length (p : ReferencePacket w d) :
    ((p.entry ++ List.ofFn p.extension).flatMap wordBits).length = p.offset := by
  rw [wordData_length, List.length_append, List.length_ofFn, ReferencePacket.offset, Nat.mul_comm]

/-- The reference field occupies exactly the last `d` bits. -/
theorem ReferencePacket.bits_length (p : ReferencePacket w d) : p.bits.length = p.offset+d := by
  rw [ReferencePacket.bits,List.length_append,packetPrefix_length,List.length_ofFn]

/-- Reading the addressed advice bit in the reference field returns its genuine index bit. -/
theorem ReferencePacket.reference_at (p : ReferencePacket w d) (i : Fin d) :
    p.bits[p.offset+i.val]? = some (p.reference i) := by
  rw [ReferencePacket.bits,List.getElem?_append_right (by rw [packetPrefix_length]; omega),
    packetPrefix_length,Nat.add_sub_cancel_left]
  simp

variable {pc reg k routines m g R r a : ℕ} {Q Γ : Type} [Fintype Q]
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)
variable (S : SiteData R r reg k w a)

/-- Pin one real literal bit per processor to the corresponding packet position.
Outside the packet the designated position is canonically zero. -/
def SiteData.withPacket (pack : Fin (R+1) → ReferencePacket w d) : SiteData R r reg k w a :=
  { S with advice := fun u j => (pack u).bits[j.val]?.getD false }

/-- The native gather installs every reference bit of H* at the frame's starbase.
The reference contents are derived from the actual pinned literal assignments. -/
theorem gather_reference (pack : Fin (R+1) → ReferencePacket w d) (link n e : ℕ)
    (fit : Fits P lib r w a R link n e) (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (mem : Memory w)
    (f : BroadcastFrame) (A : AdviceLayout) :
    let G := wiring P lib (S.withPacket pack) d link n e fit
    let L := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    f.At (readings pub) (readings mem) → Frame L (readings pub) (readings mem) → F.ContainsInput mem →
    A.At (readings pub) (readings mem) → f.Fits w (pub 0).val → A.Fits f w (pub 0).val →
    A.offset = adviceOffset P lib r w n → (pack u).offset+d ≤ A.count →
    starbase = A.dst + (pack u).offset →
    TestRun pub mac readLiteralAdvice s mem (literalAdviceSetup.slots+A.count*(literalAdviceBit.slots+1)+1)
      True (fun z => z.mem = A.copied f (readings mem) A.count ∧
        ∀ i : Fin d, z.mem (starbase+i.val) = (TeamTapeInputEmit.word w ((pack u).reference i).toNat).val) := by
  intro G L F broadcast pins physical fields room fits off count star
  have installed := gather_advice P lib (S.withPacket pack) d link n e fit u pin ext ibase hbase starbase
    pub mac s mem f A broadcast pins physical fields room fits off
  have procs : f.processors = r := broadcast.2.2.1.symm.trans pins.processors
  have enough : A.count ≤ r := procs ▸ fits.count
  apply installed.mono le_rfl Iff.rfl
  rintro z ⟨image, allBits⟩
  refine ⟨image, fun i => ?_⟩
  have hval := i.isLt
  have hi : (pack u).offset+i.val < A.count := by omega
  let j : Fin r := ⟨(pack u).offset+i.val, hi.trans_le enough⟩
  have atSite := allBits j hi
  rw [star,Nat.add_assoc]
  change z.mem (A.dst+j.val) = _
  rw [atSite]
  change (TeamTapeInputEmit.word w ((pack u).bits[(pack u).offset+i.val]?.getD false).toNat).val = _
  rw [(pack u).reference_at, Option.getD_some]

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
