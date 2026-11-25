import OAI.Computability.BorderVNP.RoutingISAAdviceProof
import OAI.Computability.BorderVNP.TransmissionPinsInput

/-! # The advice array contains bits of the actual initialized processor literals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

variable {w : ℕ} {f : BroadcastFrame} {a : AdviceLayout} {L : Pins.Layout}
  {pub : Arg → Word w} {m : Memory w}

private theorem same_geometry (broadcast : f.At (readings pub) (readings m))
    (pins : Pins.Frame L (readings pub) (readings m)) :
    f.processors = L.processors ∧ f.literal = L.literal ∧ f.stride = L.stride := by
  obtain ⟨_,teams,proc,lit,link,_,_⟩ := broadcast
  refine ⟨proc.symm.trans pins.processors,lit.symm.trans pins.literal,?_⟩
  rw [BroadcastFrame.stride,Pins.Layout.stride,Pins.Layout.offset,teams.symm.trans pins.teams,
    lit.symm.trans pins.literal,link.symm.trans pins.link]
  omega

/-- A physical advice word is the actual specified bit of the specified
processor's original literal field, including program-prefix bits. -/
theorem AdviceLayout.src_literal {r : Pins.ProcessorFields L}
    (broadcast : f.At (readings pub) (readings m)) (pins : Pins.Frame L (readings pub) (readings m))
    (input : r.ContainsInput m) (i : Fin L.processors)
    (j : Fin L.literal) (off : j.val = a.offset) :
    m (a.src f i) = TeamTapeInputEmit.headerWord w (r.literal i) j := by
  have h := (same_geometry broadcast pins).2.2
  simpa only [src,h,← off] using input.literal i j

private theorem headerWord_lt_two (bits : List Bool) (i : ℕ) :
    (TeamTapeInputEmit.headerWord w bits i).val < 2 := by
  have hb : (bits[i]?.getD false).toNat ≤ 1 := by cases (bits[i]?.getD false) <;> decide
  change (bits[i]?.getD false).toNat % 2^w < 2
  exact (Nat.mod_le ..).trans_lt (by omega)

/-- Every source word of the fitted copy is Boolean by the initialized tape
layout; no separate advice-bit premise is needed. -/
theorem AdviceLayout.source_bits {r : Pins.ProcessorFields L}
    (broadcast : f.At (readings pub) (readings m)) (pins : Pins.Frame L (readings pub) (readings m))
    (input : r.ContainsInput m) (room : a.Fits f w (pub 0).val) :
    ∀ i < a.count, readings m (a.src f i) < 2 := by
  intro i hi
  obtain ⟨procs,lit,_⟩ := same_geometry broadcast pins
  let k : Fin L.processors := ⟨i,procs ▸ hi.trans_le room.count⟩
  let j : Fin L.literal := ⟨a.offset,lit ▸ room.literal⟩
  change (m (a.src f k)).val < 2
  rw [AdviceLayout.src_literal broadcast pins input k j rfl]
  exact headerWord_lt_two (r.literal k) j

/-- The accepted startup execution copies bits from the actual parser fields
to consecutive destination addresses and preserves every other physical word. -/
theorem readLiteralAdvice_processorFields (macros : TeamOpcode.Macros w 8) (s : Bank w)
    (r : Pins.ProcessorFields L) (broadcast : f.At (readings pub) (readings m))
    (pins : Pins.Frame L (readings pub) (readings m)) (input : r.ContainsInput m)
    (fields : a.At (readings pub) (readings m))
    (fit : f.Fits w (pub 0).val) (room : a.Fits f w (pub 0).val) :
    TestRun pub macros readLiteralAdvice s m (literalAdviceSetup.slots+a.count*(literalAdviceBit.slots+1)+1)
      True (fun z => z.mem = a.copied f (readings m) a.count ∧
        (∀ j : Reg, j.val < 30 → z.reg j = (s j).val) ∧
        ∀ i : Fin L.processors, i.val < a.count → ∀ j : Fin L.literal, j.val = a.offset →
          z.mem (a.dst+i) = (TeamTapeInputEmit.headerWord w (r.literal i) j).val) := by
  apply (readLiteralAdvice_test f a pub macros s m broadcast fields fit room
    (AdviceLayout.source_bits broadcast pins input room)).mono le_rfl Iff.rfl
  rintro z ⟨hm,hr⟩
  refine ⟨hm,hr,?_⟩
  intro i hi j off
  rw [hm,a.copied_at f (readings m) hi]
  exact congrArg Fin.val (AdviceLayout.src_literal broadcast pins input i j off)

end RoutingISA

end BorderVNP
end Computability
end OAI
