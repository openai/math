import OAI.Computability.BorderVNP.TransmissionSiteWiring
import OAI.Computability.BorderVNP.RoutingISAAdviceInput

/-! # Reading the distributed reference index from the physical signed processor literals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM UniversalMachine TeamTapeHandoff RoutingISA RoutingISA.Pins

variable {p reg k routines m g R r w a : ℕ} {Q Γ : Type} [Fintype Q]
variable (physical : VPVNP.UniversalMachine.Program)
variable (P : TeamOpcode.Program p reg k routines) (lib : Fin routines → TeamSite.Macro Q Γ m g)
variable (S : SiteData R r reg k w a)

/-- Absolute literal offset of the distributed advice bit on every processor, after its
program prefix, four compact startup parameters, and padded control metadata. -/
noncomputable def adviceOffset (r w n : ℕ) : ℕ :=
  (programPrefix (TeamSite.Processor.machine P lib)).length + cutWidth n + setupWidth (w+1) n +
    prefixCapacity r k reg w n

/-- Absolute advice-bit offset of an arbitrary physically installed interpreter. -/
noncomputable def adviceOffsetWith (r k reg w n : ℕ) : ℕ :=
  (programPrefix physical).length + cutWidth n + setupWidth (w+1) n + prefixCapacity r k reg w n

/-- The actual word loaded from the common literal offset encodes this processor's chosen
advice bit, including at the first owner and at sites with a second virtual block. -/
theorem literal_adviceWith (d link n e : ℕ) (fit : fitsWith physical reg k r w a R link n e) (u : Fin (R+1)) (j : Fin r)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ) :
    let G := wiringWith physical P S d link n e fit
    let F := G.processorFields u pin ext ibase hbase starbase
    TeamTapeInputEmit.headerWord w (F.literal j) (adviceOffsetWith physical r k reg w n) =
      TeamTapeInputEmit.word w (S.advice u j).toNat := by
  intro G F
  let pr := physical
  let stride := entryStride pr (w+1) n (prefixCapacity r k reg w n+1+a) R link
  let interior := Wires.innerWidth r reg w e (w+1)
  let first := programPrefix pr ++ TeamTapeInput.parameters (TeamTapeInput.digits n stride)
    (TeamTapeInput.digits n interior) ++ TeamTapeInput.Entry.setupBits (w+1) n (j.val*stride) (2^e)
  let last := payload (S.publicWords u) S.block S.limit S.burst
    (S.start P u) j e n (S.advice u j) (S.free u j)
  have split : F.literal j = first ++ last := by
    change programPrefix pr ++ List.ofFn (cutTail n stride interior
      (entryTail (w+1) n (j.val*stride) (2^e) (S.siteBits P n e u j))) = _
    rw [ofFn_cutTail,ofFn_entryTail,SiteData.siteBits,ofFn_payloadBits]
    simp only [first,last,List.append_assoc]
  have length : adviceOffsetWith physical r k reg w n = first.length + prefixCapacity r k reg w n := by
    simp [first,adviceOffsetWith,pr,cutWidth,length_setupBits,TeamTapeInput.length_parameters,Nat.add_assoc]
  have bit : last[prefixCapacity r k reg w n]? = some (S.advice u j) := payload_advice ..
  simp only [TeamTapeInputEmit.headerWord, split, length, List.getElem?_append_right (by omega :
    first.length ≤ first.length+prefixCapacity r k reg w n), Nat.add_sub_cancel_left,bit,Option.getD_some]

/-- The ordinary signed processor instance of the program-indexed result. -/
theorem literal_advice (d link n e : ℕ) (fit : Fits P lib r w a R link n e) (u : Fin (R+1)) (j : Fin r)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ) :
    let G := wiring P lib S d link n e fit
    let F := G.processorFields u pin ext ibase hbase starbase
    TeamTapeInputEmit.headerWord w (F.literal j) (adviceOffset P lib r w n) =
      TeamTapeInputEmit.word w (S.advice u j).toNat :=
  literal_adviceWith (TeamSite.Processor.machine P lib) P S d link n e fit u j pin ext ibase hbase starbase

/-- After the real native gather, all addressed words of the copied packet have the
actual assigned literal bits; outside the packet the original memory is retained. -/
theorem gather_adviceWith (d link n e : ℕ) (fit : fitsWith physical reg k r w a R link n e) (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (mem : Memory w)
    (f : BroadcastFrame) (A : AdviceLayout) :
    let G := wiringWith physical P S d link n e fit
    let L := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    f.At (readings pub) (readings mem) → Frame L (readings pub) (readings mem) → F.ContainsInput mem →
    A.At (readings pub) (readings mem) → f.Fits w (pub 0).val → A.Fits f w (pub 0).val →
    A.offset = adviceOffsetWith physical r k reg w n →
    TestRun pub mac readLiteralAdvice s mem (literalAdviceSetup.slots+A.count*(literalAdviceBit.slots+1)+1)
      True (fun z => z.mem = A.copied f (readings mem) A.count ∧
        ∀ i : Fin r, i.val < A.count → z.mem (A.dst+i.val) = (TeamTapeInputEmit.word w (S.advice u i).toNat).val) := by
  intro G L F broadcast pins input fields frameRoom room off
  have lit : f.literal = L.literal := broadcast.2.2.2.1.symm.trans pins.literal
  have literal : A.offset < L.literal := lit ▸ room.literal
  have result := readLiteralAdvice_processorFields mac s F broadcast pins input fields frameRoom room
  apply result.mono le_rfl Iff.rfl
  rintro z ⟨image,_,copied⟩
  refine ⟨image, fun i hi => ?_⟩
  let j : Fin L.literal := ⟨A.offset,literal⟩
  have loaded := copied i hi j rfl
  have bit := literal_adviceWith physical P S d link n e fit u i pin ext ibase hbase starbase
  change z.mem (A.dst+i.val) = (TeamTapeInputEmit.headerWord w (F.literal i) A.offset).val at loaded
  rw [off] at loaded
  exact loaded.trans (congrArg Fin.val bit)

/-- The ordinary signed processor instance of the program-indexed result. -/
theorem gather_advice (d link n e : ℕ) (fit : Fits P lib r w a R link n e) (u : Fin (R+1))
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (ibase hbase starbase : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (mem : Memory w)
    (f : BroadcastFrame) (A : AdviceLayout) :
    let G := wiring P lib S d link n e fit
    let L := G.pinLayout u ibase hbase starbase
    let F := G.processorFields u pin ext ibase hbase starbase
    f.At (readings pub) (readings mem) → Frame L (readings pub) (readings mem) → F.ContainsInput mem →
    A.At (readings pub) (readings mem) → f.Fits w (pub 0).val → A.Fits f w (pub 0).val →
    A.offset = adviceOffset P lib r w n →
    TestRun pub mac readLiteralAdvice s mem (literalAdviceSetup.slots+A.count*(literalAdviceBit.slots+1)+1)
      True (fun z => z.mem = A.copied f (readings mem) A.count ∧
        ∀ i : Fin r, i.val < A.count → z.mem (A.dst+i.val) = (TeamTapeInputEmit.word w (S.advice u i).toNat).val) :=
  gather_adviceWith (TeamSite.Processor.machine P lib) P S d link n e fit u pin ext ibase hbase starbase pub mac s mem f A

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
