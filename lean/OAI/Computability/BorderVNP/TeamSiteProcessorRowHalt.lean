import OAI.Computability.BorderVNP.TeamSiteProcessorRow
import OAI.Computability.BorderVNP.TeamSiteWitness

/-! # Physical processor rows after the native RAM has accepted

A canonical halted predecessor consumes no branch choices. The local clock, physical
successor comparison and occupied sort lanes are still checked on each such row. Its
initialization records are the entire row presented to the sorter.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Processor.Row

open VPVNP BurstRAM RAMTape Layout TeamTapeHandoff TeamPrivateFragment

variable {Q Γ : Type} {p r k a m g n d e w : ℕ}
variable {P : TeamOpcode.Program p r k a} {lib : Fin a → Macro Q Γ m g}
variable (X : Context P lib n d e w)

/-- Exact terminal execution after a prior acceptance, including on wrong successor
bits, an excessive global tick, or malformed comparison messages. -/
theorem Context.halted_model (elapsed : Word w) (frame : X.frame = .accepted elapsed) :
    X.Model [] (some false)
      (Endpoint.haltValid X.last r elapsed X.limit (X.base .outgoing) = true ∧ X.sorted [])
      (X.cost 0 []) := by
  have ready : (X.base ∘ endpoint) ∘ Endpoint.startup = TeamLocalClock.Startup.input
      X.pub X.block X.limit X.cap ((Frame.accepted elapsed : Frame w r).bits ++ []) := by
    simpa only [frame, List.append_nil, Function.comp_assoc] using X.startup
  obtain ⟨t,ht,out,ep,_,preserve⟩ := Endpoint.halted_run P lib X.last P.base.entry X.fits X.pub
    X.block X.limit elapsed X.cap [] [] (X.base ∘ endpoint) ready X.payload
  have bufferEq : out ∘ Endpoint.Port.site ∘ probe ∘ TeamProbeEmit.Port.buffer =
      (X.base ∘ site) ∘ probe ∘ TeamProbeEmit.Port.buffer :=
    funext fun j => preserve (probe (.buffer j))
  apply X.finish [] (some false) _ 0 (by omega) ep
  have noEvents : X.slots [] = X.initial := List.append_nil _
  rw [bufferEq,noEvents]
  exact X.work.buffer

/-- The logical endpoint relation for this branch names the single empty event list
and the propagated time. The frame guard compares the same bits as the actual tape. -/
theorem Context.halt_pass_iff (elapsed : Word w) (frame : X.frame = .accepted elapsed)
    (macros : TeamOpcode.Macros w a) :
    (Endpoint.haltValid X.last r elapsed X.limit (X.base .outgoing) = true ∧ X.sorted []) ↔
      ∃ output, EndpointRow P X.pub macros X.block X.limit X.cap X.frame [] output ∧
        X.guard output = true ∧ X.sorted [] := by
  cases last : X.last <;> simp [Endpoint.haltValid,Context.guard,EndpointRow,frame,last,Frame.halted,
    and_assoc]


/-- On the actual bounded signed machine the only possible accepting leaf after a
prior halt is the empty choice word with positive sign. It occurs exactly when the
clock, successor frame, and local sorter all accept. -/
theorem Context.halted_leaf_iff (elapsed : Word w) (frame : X.frame = .accepted elapsed)
    (clock : ℕ) (fits : X.cost 0 [] ≤ clock) (bits : List Bool) (z : Bool) :
    (bits,z) ∈ TeamContraction.Replay.leaves (code P lib) negative clock start
      (StackCompiler.labeledInput input X.raw) ↔
      bits = [] ∧ z = false ∧ Endpoint.haltValid X.last r elapsed X.limit (X.base .outgoing) = true ∧
        X.sorted [] := by
  rw [TeamContraction.Replay.mem_leaves_iff]
  obtain ⟨t,ht,q,out,b,run,halt,valid,_,sign⟩ := X.halted_model elapsed frame
  constructor
  · rintro ⟨t',_,q',s',other,accept,sg⟩
    have withBits := TeamSiteWitness.append_choices run bits
    simp only [List.nil_append] at withBits
    have accept' : replay (code P lib) (q',[]) = .halt true := by simp [replay,accept]
    have halt' : replay (code P lib) (q,bits) = .halt b := by simp [replay,halt]
    obtain ⟨_,same,_⟩ := TeamContraction.Replay.terminal_unique other withBits accept' halt'
    obtain ⟨rfl,empty⟩ := Prod.mk.inj same
    have yes := StackOp.halt.inj (halt.symm.trans accept)
    exact ⟨empty.symm,sg.symm.trans (sign yes),(valid.mp yes).1⟩
  · rintro ⟨rfl,rfl,pass,sorted⟩
    have yes := valid.mpr ⟨⟨pass,sorted⟩,rfl⟩
    exact ⟨t,ht.trans_le fits,q,out,run,yes ▸ halt,sign yes⟩

end TeamSite.Processor.Row

end BorderVNP
end Computability
end OAI
