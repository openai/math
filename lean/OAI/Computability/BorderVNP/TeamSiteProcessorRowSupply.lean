import OAI.Computability.BorderVNP.TeamSiteProcessorRowLive
import OAI.Computability.BorderVNP.TeamSiteProcessorRowHalt

/-! # Complete physical processor models for all branch supplies

Every infinite supply determines a finite physical prefix. It either rejects before
reaching a consistent typed block, or is the exact bit spelling of a genuine native
row. Its outgoing frame and physical sorter still test their arbitrary proposed bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Processor.Row

open VPVNP BurstRAM RAMTape RAMSerialization TeamPrivateFragment Layout TeamTapeHandoff TeamLocalClock
open TeamSiteChoices TeamSiteEvents SupplyRun RAMTape.PublicExprMachine

variable {Q Γ : Type} {p r k a m g n d e w : ℕ}
variable {P : TeamOpcode.Program p r k a} {lib : Fin a → Macro Q Γ m g}
variable (X : Context P lib n d e w)

private theorem model_cast {bits sg pass pass' T T'} (h : X.Model bits sg pass T)
    (he : pass ↔ pass') (ht : T ≤ T') : X.Model bits sg pass' T' := by
  have h' := propext he
  subst pass'
  obtain ⟨t,time,q,out,b,rest⟩ := h
  exact ⟨t,time.trans_le ht,q,out,b,rest⟩

/-- A genuine typed endpoint row has the full physical model, whether live or propagated. -/
theorem Context.forward (fuel : ℕ) (es : List (TeamRAM.Event w)) (out : Frame w r)
    (cert : EndpointRow P X.pub (macros lib fuel) X.block X.limit X.cap X.frame es out) :
    X.Model (chunkBits es) (chunkSign (some false) es) (X.guard out = true ∧ X.sorted es)
      (X.cost (nativeCost w m g fuel es) es) := by
  cases hf : X.frame with
  | live pc regs elapsed => exact X.forward_live fuel pc elapsed regs hf cert
  | accepted elapsed =>
    rw [hf] at cert
    obtain ⟨rfl,safe,rfl⟩ := cert
    apply model_cast X (X.halted_model elapsed hf)
    · cases h : X.last <;> simp [Endpoint.haltValid,Context.guard,h,safe,Frame.halted]
    · unfold Context.cost Budget.endpoint; omega

/-- One of the two genuine alternatives for a physical branch supply. -/
def Context.Supplied (fuel : ℕ) (u : Supply) : Prop :=
  (∃ bits sg clock, Prefix u bits ∧ X.Model bits sg False clock) ∨
  ∃ es out, Prefix u (chunkBits es) ∧ EndpointRow P X.pub (macros lib fuel) X.block X.limit X.cap X.frame es out ∧
    X.Model (chunkBits es) (chunkSign (some false) es) (X.guard out = true ∧ X.sorted es)
      (X.cost (nativeCost w m g fuel es) es)

private theorem invalid (bits : List Bool) (q : Endpoint.Label P Q m g) {t out}
    (hr : StackRuns (replay (Endpoint.code P lib)) t (.startup X.last (Startup.entry p r),bits)
      (X.base ∘ endpoint) (q,[]) out)
    (bad : Endpoint.code P lib q = .halt false) (away : ∀ sg, q ≠ .done sg) :
    X.Model bits none False (X.preludeTicks+t+1) := by
  have pre := replay_segment X.prelude bits
  have endRun := endpoint_replay P lib hr X.base rfl
  have eq : code P lib (.block q) = .halt false := by
    cases q with
    | done sg => exact (away sg rfl).elim
    | _ => simp only [code,bad,StackOp.rename]
  exact ⟨_,by omega,_,_,false,pre.trans endRun,eq,by simp,fun z => by simp [Checked],by simp⟩

private theorem invalidStartup (fuel : ℕ) (u : Supply) (bad : Startup.result p X.frame X.limit = .reject) :
    X.Supplied fuel u := by
  obtain ⟨t,_,pre⟩ := Endpoint.predecessor_run P lib X.last X.fits X.pub X.frame X.block X.limit X.cap
    [] [] (X.base ∘ endpoint) (by simpa only [List.append_nil,Function.comp_assoc] using X.startup)
  rw [bad] at pre
  exact Or.inl ⟨[],none,_,prefix_nil _,invalid X [] .invalid pre rfl (by simp)⟩

private theorem suppliedLive (fuel : ℕ) (bound : ∀ j vs, vs.length ≤ X.cap.val →
    (lib j).bounded fuel (vs : List (Word w))) (u : Supply)
    (s : TeamOpcode.State w p r) (elapsed : Word w)
    (frame : X.frame = .live (packed w s.pc.val) s.reg elapsed) (safe : elapsed ≤ X.limit) :
    X.Supplied fuel u := by
  let c := X.window elapsed
  let base := X.loopBank s elapsed
  have safety := X.windowSafe elapsed safe
  obtain ⟨es,z,fin,v,h⟩ := exists_run P X.pub lib fuel s c u safety bound
  have ch := h.chunk
  have stopped := h.stopped
  have pre := h.prefix
  have finish (out : Frame w r) (cert : EndpointRow P X.pub (macros lib fuel) X.block X.limit X.cap X.frame es out) :
      X.Supplied fuel u := Or.inr ⟨es,out,pre,cert,X.forward fuel es out cert⟩
  cases v with
  | accepted =>
    have guard : exit P X.pub z fin = .accepted := by cases stopped; assumption
    have hb := noncallback_bank P X.pub z fin (fun _ => by simp [guard])
    apply finish (.accepted fin.elapsed)
    rw [frame]
    exact ⟨safe,s.pc,z,fin,rfl,ch,Or.inl ⟨Prod.ext guard hb,rfl⟩⟩
  | handoff =>
    have guard : exit P X.pub z fin = .handoff z.pc := by cases stopped; assumption
    have hb := noncallback_bank P X.pub z fin (fun _ => by simp [guard])
    apply finish (.live (packed w z.pc.val) z.reg fin.elapsed)
    rw [frame]
    exact ⟨safe,s.pc,z,fin,rfl,ch,Or.inr ⟨Prod.ext guard hb,rfl⟩⟩
  | reject =>
    obtain ⟨t,q,b,_,run,bad,_⟩ := h.replay P X.pub lib fuel (some false) X.initial base []
      safety (X.loopBank_clock ..) (X.loopBank_work ..) X.space
    rw [List.append_nil] at run
    obtain ⟨time,_,z',out,hend,halt,away,_⟩ := Endpoint.live_reject P lib X.last X.fits X.pub s
      X.block X.limit elapsed X.cap safe [] (chunkBits es) [] (X.base ∘ endpoint)
      (by simpa only [List.append_nil,Function.comp_assoc,frame] using X.startup) t q b run bad.1 bad.2
    exact Or.inl ⟨chunkBits es,none,_,pre,invalid X _ z' hend halt away⟩

/-- Complete supply interpretation for arbitrary typed predecessor frames, including
word-PC values outside the fixed instruction table and already halted predecessors. -/
theorem Context.supply (fuel : ℕ) (bound : ∀ j vs, vs.length ≤ X.cap.val →
    (lib j).bounded fuel (vs : List (Word w))) (u : Supply) : X.Supplied fuel u := by
  by_cases safe : X.frame.elapsed ≤ X.limit
  · cases hf : X.frame with
    | live word regs elapsed =>
      have ok : elapsed ≤ X.limit := by simpa only [hf,Frame.elapsed] using safe
      by_cases valid : word.val < p
      · let pc : Fin p := ⟨word.val,valid⟩
        have eq : packed w pc.val = word := Fin.ext (packed_val word.isLt)
        exact suppliedLive X fuel bound u ⟨pc,regs⟩ elapsed (by simpa only [eq] using hf) ok
      · apply invalidStartup X fuel u
        simp [Startup.result,hf,Frame.elapsed,ok,(TeamLocalClockPC.lookup_reject_iff ..).mpr (Nat.le_of_not_gt valid)]
    | accepted elapsed =>
      have ok : elapsed ≤ X.limit := by simpa only [hf,Frame.elapsed] using safe
      have cert : EndpointRow P X.pub (macros lib fuel) X.block X.limit X.cap X.frame [] (.accepted elapsed) := by
        rw [hf]; exact ⟨rfl,ok,rfl⟩
      exact Or.inr ⟨[],.accepted elapsed,prefix_nil _,cert,X.forward fuel [] _ cert⟩
  · apply invalidStartup X fuel u
    simp [Startup.result,safe]

end TeamSite.Processor.Row

end BorderVNP
end Computability
end OAI
