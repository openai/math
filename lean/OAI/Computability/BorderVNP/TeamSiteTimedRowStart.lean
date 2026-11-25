import OAI.Computability.BorderVNP.TeamSiteTimedPostlude

/-! # Actual trusted-clock row startup on every predecessor frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor.Row

open VPVNP RAMTape RAMTape.PublicExprMachine BurstRAM TeamLocalClock TeamPrivateFragment TeamTapeHandoff
variable {Q Γ : Type} {p r k a m g n d e w : ℕ} {P : TeamOpcode.Program p r k a}
variable {lib : Fin a → Macro Q Γ m g} {mark : Fin a → Γ}
variable (X : Site P lib mark n d e w)
local notation "old" => Processor.code P (fun j => extend (lib j) (mark j))
local notation "initial" => TrustedClock.installed (Layout.input (r:=r) (k:=k) (d:=(m+1)*g)) X.raw
local notation "result" => Startup.result p X.frame X.limit
local notation "decoded" => Startup.decoded X.pub X.frame X.block (Startup.remaining p X.frame X.limit) X.cap []

/-- The physically installed ordinary site after the incoming frame is decoded. -/
noncomputable def decodedSite :=
  installStacks Processor.endpoint X.base (installStacks Endpoint.startup (X.base ∘ Processor.endpoint) decoded)

/-- The installed trusted timer and the physically decoded incoming frame. -/
noncomputable def startBank := installStacks TeamClocked.Port.user initial (decodedSite X)

/-- The deterministic prefix up to the decoded predecessor, just before the
ordinary and timed machines leave startup. No private callback can occur here. -/
theorem decoded_before :
    ∃ t ≤ X.preludeTicks+Startup.budget r w,
      StackRuns old t Processor.start (StackCompiler.labeledInput Layout.input X.raw)
        (.block (.startup X.last (.done result))) (decodedSite X) := by
  let lib' := fun j => extend (lib j) (mark j)
  obtain ⟨t,ht,run⟩ := Startup.run p X.fits X.pub X.frame X.block X.limit X.cap []
  rw [List.append_nil] at run
  let base := X.base ∘ Processor.endpoint
  have hr := run.lift Endpoint.startup Endpoint.startup_injective (Endpoint.Label.startup (P:=P) X.last) base
    (target:=Endpoint.code P lib') (by intro q h; cases q with | done res => cases res <;> contradiction | _ => rfl)
  rw [installStacks_eq Endpoint.startup_injective base _ (congrFun X.startup)] at hr
  have hp := hr.lift Processor.endpoint Processor.endpoint_injective Processor.Label.block X.base (target:=old)
    (by intro q h; cases q <;> first | rfl | simp [Endpoint.code] at h)
  rw [installStacks_eq Processor.endpoint_injective X.base base (fun _ => rfl)] at hp
  exact ⟨_,by omega,X.prelude.trans hp⟩

/-- The ordinary and metered tables have the same deterministic execution up to the
decoded incoming frame. Only the metered table carries the trusted template. -/
theorem decoded_start (bits : List Bool) :
    ∃ t ≤ X.preludeTicks+Startup.budget r w+1,
      StackRuns (replay old) t (Processor.start,bits) (StackCompiler.labeledInput Layout.input X.raw)
        (.block (Endpoint.afterStartup X.last result),bits) (decodedSite X) ∧
      StackRuns (replay (code P lib mark)) t (.site Processor.start,bits) initial
        (.site (.block (Endpoint.afterStartup X.last result)),bits) (startBank X) := by
  obtain ⟨t,ht,oldPrefix⟩ := decoded_before X
  have earlier : ¬ TrustedClock.afterStartup P (.block (.startup X.last (.done result)) : Processor.Label P Q (m+1) g) :=
    not_false
  have newPrefix := prelude_run P lib mark X.raw oldPrefix earlier
  have lastOld : StackRuns old 1 (.block (.startup X.last (.done result))) (decodedSite X)
      (.block (Endpoint.afterStartup X.last result)) (decodedSite X) := .cons (.goto rfl) (.nil ..)
  have lastNew : StackRuns (code P lib mark) 1 (.site (.block (.startup X.last (.done result)))) (startBank X)
      (.site (.block (Endpoint.afterStartup X.last result))) (startBank X) := .cons (.goto rfl) (.nil ..)
  exact ⟨_,by omega,replay_segment (oldPrefix.trans lastOld) bits,replay_segment (newPrefix.trans lastNew) bits⟩

/-- Out-of-range predecessor counters and clocks reject at the actual invalid label. -/
theorem invalid_startup (bad : result = .reject) : ∃ T, Model X [] none False T := by
  obtain ⟨t,_,_,run⟩ := decoded_start X []
  rw [bad] at run
  exact ⟨t+1,t,by omega,_,_,false,run,rfl,by simp,fun z => by simp [Checked,Endpoint.afterStartup],by simp⟩

/-- A genuine live predecessor installs its true clock and registers in the
same work bank as the initialized time-zero records. -/
theorem start_live (s : TeamOpcode.State w p r) (elapsed : Word w)
    (frame : X.frame = .live (packed w s.pc.val) s.reg elapsed) (safe : elapsed ≤ X.limit)
    (bits : List Bool) :
    ∃ t ≤ X.preludeTicks+Startup.budget r w+1,
      StackRuns (replay (code P lib mark)) t (.site Processor.start,bits) initial
        (loopLabel X.last (.clock (some false) (.enter s.pc)),bits) (startBank X) ∧
      startBank X ∘ loopPort = X.loopBank s elapsed ∧ MeterReady (startBank X) (X.raw.length^25) := by
  obtain ⟨t,ht,_,run⟩ := decoded_start X bits
  have hv : (packed w s.pc.val).val = s.pc.val := packed_val (lt_of_lt_of_le s.pc.isLt X.fits)
  have hl : TeamLocalClockPC.lookup p s.pc.val = .live s.pc := by
    simpa only [hv] using TeamLocalClockPC.lookup_packed s.pc X.fits
  simp only [frame,Startup.result,Frame.elapsed,safe,ite_true,hv,hl] at run
  refine ⟨t,ht,run,?_,(installed_ready X.raw).install _⟩
  have hremaining : Startup.remaining p X.frame X.limit = packed w (X.limit.val-elapsed.val) := by
    simp only [frame,Startup.remaining,hv,s.pc.isLt,safe,and_self,ite_true]
  have read (j : TeamSite.Port r k ((m+1)*g)) :
      startBank X (loopPort j) = installStacks Endpoint.startup (X.base ∘ Processor.endpoint) decoded (.site j) :=
    (installStacks_at (fun _ _ => TeamClocked.Port.user.inj) initial (decodedSite X) (Layout.site j)).trans
      (installStacks_at Processor.endpoint_injective X.base _ (.site j))
  have he := Endpoint.startup_site (X.base ∘ Processor.endpoint) X.pub s.pc (packed w s.pc.val) s.reg X.block
    (packed w (X.limit.val-elapsed.val)) elapsed X.cap []
  funext j
  rw [Function.comp_apply,read,hremaining,frame]
  exact congrFun he j

/-- A physical rejected chunk before sorting determines a zero terminal on its
complete consumed spelling, regardless of any earlier signed private result. -/
theorem rejected_loop_model (s z : TeamOpcode.State w p r) (elapsed : Word w)
    (frame : X.frame = .live (packed w s.pc.val) s.reg elapsed) (safe : elapsed ≤ X.limit)
    (bits : List Bool) (sg : Option Bool) {steps q out}
    (run : StackRuns (replay (code P lib mark)) steps
      (loopLabel X.last (.clock (some false) (.enter s.pc)),bits) (startBank X) (q,[]) out)
    (bad : outcome P lib mark X.last sg z.pc q .reject) : ∃ T, Model X bits none False T := by
  obtain ⟨t,_,pre,_,_⟩ := start_live X s elapsed frame safe bits
  obtain ⟨⟨q,rfl⟩,halt⟩ := bad
  exact ⟨t+steps+1,_,by omega,_,_,false,pre.trans run,halt,by simp,fun z => by simp [Checked],by simp⟩

end TeamSite.TimedProcessor.Row

end BorderVNP
end Computability
end OAI
