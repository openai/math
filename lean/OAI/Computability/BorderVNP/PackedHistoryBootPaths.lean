import OAI.Computability.BorderVNP.PackedHistoryGeometryBranch
import OAI.Computability.BorderVNP.DiagonalNativeEvalStartup
import OAI.Computability.BorderVNP.TransmissionStartupArena

/-! # Attaching the common-header and branch instructions to the geometry returns -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots JointHeader DiagonalResidueRAM

/-- The actual contiguous startup arena protects the input, the 112 frame words and the
entire common header from the subsequent substituted and live-copy writes. -/
theorem arena_pin_clear {w d : ℕ} (arena : StartupArena) (u : Fin arena.teams) (off : ℕ)
    (packet : ReferencePacket w d) :
    let L := (arena.operands u off packet).layout
    PinClear L 0 (L.processors*L.stride) ∧ PinClear L arena.frame 112 ∧
      PinClear L arena.broadcastBase arena.header := by
  intro L
  have str : L.stride = arena.stride := by
    change arena.literal+(arena.teams-1)*arena.link+arena.literal = 2*arena.literal+(arena.teams-1)*arena.link
    omega
  have iv : L.ibase = arena.frame+112+arena.copied+arena.header := rfl
  have hv : L.hbase = arena.frame+112+arena.copied+arena.header+arena.count := rfl
  have total : L.processors*L.stride = arena.frame := by rw [str]; rfl
  have bcast : arena.broadcastBase = arena.frame+112+arena.copied := rfl
  simp only [PinClear,total,bcast,iv,hv]; omega

/-- The physical startup, copy, positive branch-word probe and conditional jump extend the
actual returning evaluation paths bijectively. They leave the returned words intact and add
their own measured number of ticks plus the two dispatch instructions. -/
theorem ProfilePaths.with_startup {w o k time dest : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {bank : Bank w} {mem : Memory w} {body : Code} {ok : Prop} {words : Fin o → ℕ} {resident : (Fin k → Bool) → Memory w → Prop}
    (f : BroadcastFrame) {trace ready saved} (boot : Runs pub mac bootHeader bank mem trace ready saved)
    (stable : f.Stable (readings ready)) (mode : (saved f.dst).val ≠ 0)
    (inside : ProfilePaths body k pub mac (Function.update ready 10 (saved f.dst)) saved ok time dest words resident) :
    ProfilePaths (withStartup body) k pub mac bank mem ok (traceCost trace+2+time) dest words resident := by
  obtain ⟨u,mu,pre,header,events,start,read⟩ := Runs.seq_iff.mp boot
  let dispatch := dispatchPrefix f saved pre header
  have effects := dispatchPrefix_effects f start read
  have code : selected f body saved = body := ite_eq_right mode
  have eqv : ∃ e : Returns (selected f body saved) pub mac (Function.update ready 10 (saved f.dst)) saved ≃
      Returns (withStartup body) pub mac bank mem, ∀ z, (e z).val = (dispatch++z.val.1,z.val.2) :=
    ⟨startupReturnEquiv f body start read stable, startupReturnEquiv_val f body start read stable⟩
  rw [code] at eqv
  obtain ⟨ext,added⟩ := eqv
  have timeD : traceCost dispatch ≤ traceCost trace+2 := by
    rw [events,Transmission.cost_append,start.deterministic_cost (by decide),read.deterministic_cost (by decide)]
    exact effects.1.cost
  have bitsD : dispatch.flatMap TeamRAM.Event.choices = [] :=
    List.flatMap_eq_nil_iff.mpr fun e he => List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (effects.1.choices e he))
  refine ⟨ext.nonempty_congr.symm.trans inside.passes,?_,?_⟩
  · intro accepted
    obtain ⟨E,eff⟩ := inside.outputs accepted
    refine ⟨E.trans ext,fun g => ?_⟩
    simp only [Equiv.trans_apply,added,List.flatMap_append,bitsD,List.nil_append,Transmission.cost_append]
    have sign : signedWeight (dispatch++(E g).val.1) = 1 := by
      have plus : signedWeight dispatch = 1 := effects.2
      simpa only [signedWeight,List.map_append,List.prod_append,one_mul] using congrArg₂ (·*·) plus (eff g).2.2.1
    exact ⟨(eff g).1,Nat.add_le_add timeD (eff g).2.1,sign,(eff g).2.2.2⟩
  · intro path g choices
    obtain ⟨z,rfl⟩ := ext.surjective path
    rw [added,List.flatMap_append,bitsD,List.nil_append] at choices
    rw [added]; exact inside.memory z g choices

/-- Enlarge a verified runtime bound while retaining the same complete history equivalence. -/
theorem ProfilePaths.mono {w o k time later dest : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {bank : Bank w} {mem : Memory w} {body : Code} {ok : Prop} {words : Fin o → ℕ} {resident : (Fin k → Bool) → Memory w → Prop}
    (p : ProfilePaths body k pub mac bank mem ok time dest words resident) (h : time ≤ later) :
    ProfilePaths body k pub mac bank mem ok later dest words resident := by
  refine ⟨p.passes,fun good => ?_,p.memory⟩
  obtain ⟨E,hr⟩ := p.outputs good
  exact ⟨E,fun g => ⟨(hr g).1,((hr g).2.1).trans h,(hr g).2.2⟩⟩

/-- Project the physical resident-memory assertion to a form used by the subsequent stages. -/
theorem ProfilePaths.map_memory {w o k time dest : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {bank : Bank w} {mem : Memory w} {body : Code} {ok : Prop} {words : Fin o → ℕ}
    {source target : (Fin k → Bool) → Memory w → Prop}
    (p : ProfilePaths body k pub mac bank mem ok time dest words source) (h : ∀ g m, source g m → target g m) :
    ProfilePaths body k pub mac bank mem ok time dest words target :=
  ⟨p.passes,p.outputs,fun z g bits => h g _ (p.memory z g bits)⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
