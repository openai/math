import OAI.Computability.BorderVNP.TeamSiteTimedRowStart

/-! # Complete timed processor coverage on arbitrary physical supplies -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor.Row

open VPVNP BurstRAM RAMTape TeamTapeHandoff TeamLocalClock TeamSiteChoices TeamSiteEvents SupplyRun
open RAMTape.PublicExprMachine
variable {Q Γ : Type} {p r k a m g n d e w : ℕ} {P : TeamOpcode.Program p r k a}
variable {lib : Fin a → Macro Q Γ m g} {mark : Fin a → Γ}
variable (X : Site P lib mark n d e w)
local notation "N" => X.raw.length^25

private theorem supplied_live (hm : ∀ j, (lib j).alphabet.blank ≠ mark j) (emit : forward X N)
    (u : Supply) (s : TeamOpcode.State w p r) (elapsed : Word w)
    (frame : X.frame = .live (packed w s.pc.val) s.reg elapsed) (safe : elapsed ≤ X.limit) :
    (∃ bits sg T, Prefix u bits ∧ Model X bits sg False T) ∨
    ∃ es out, Prefix u (chunkBits es) ∧ Endpoint X N es out ∧
      Model X (chunkBits es) (chunkSign (some false) es) (X.guard out = true ∧ X.sorted es) (budget X N es) := by
  obtain ⟨_,_,_,read,meter⟩ := start_live X s elapsed frame safe []
  let c := X.window elapsed
  have clock : (startBank X ∘ loopPort) ∘ Port.clock = c.bank X.pub s := by rw [read]; exact X.loopBank_clock ..
  have work : Work.Ready X.hw₂ (2^e) X.initial (startBank X ∘ loopPort) := by rw [read]; exact X.loopBank_work ..
  obtain ⟨es,z,fin,v,ch,pre,stop,t,q,out,_,run,ok,_⟩ := supplied_run P X.pub lib mark hm N X.last s c u
    (some false) X.initial (startBank X) [] (X.windowSafe elapsed safe) clock work meter X.space
  have finish (f : Frame w r) (cert : Endpoint X N es f) :
      (∃ bits sg T, Prefix u bits ∧ Model X bits sg False T) ∨
      ∃ es out, Prefix u (chunkBits es) ∧ Endpoint X N es out ∧
        Model X (chunkBits es) (chunkSign (some false) es) (X.guard out = true ∧ X.sorted es) (budget X N es) :=
    Or.inr ⟨es,f,pre,cert,emit es f cert⟩
  cases v with
  | accepted =>
    have guard : exit P X.pub z fin = .accepted := by cases stop; assumption
    have hb := noncallback_bank P X.pub z fin (fun _ => by simp [guard])
    apply finish (.accepted fin.elapsed)
    unfold Endpoint
    rw [frame]
    exact ⟨safe,s.pc,z,fin,rfl,ch,Or.inl ⟨Prod.ext guard hb,rfl⟩⟩
  | handoff =>
    have guard : exit P X.pub z fin = .handoff z.pc := by cases stop; assumption
    have hb := noncallback_bank P X.pub z fin (fun _ => by simp [guard])
    apply finish (.live (packed w z.pc.val) z.reg fin.elapsed)
    unfold Endpoint
    rw [frame]
    exact ⟨safe,s.pc,z,fin,rfl,ch,Or.inr ⟨Prod.ext guard hb,rfl⟩⟩
  | reject =>
    rw [List.append_nil] at run
    obtain ⟨T,model⟩ := rejected_loop_model X s z elapsed frame safe _ _ run ok
    exact Or.inl ⟨chunkBits es,none,T,pre,model⟩

/-- Genuine endpoint emission and the timed site on every branch supply together
cover malformed predecessors, invalid fetches, overlarge burst addresses and native
timeouts. -/
theorem supplied_of_forward (hm : ∀ j, (lib j).alphabet.blank ≠ mark j) (emit : forward X N) :
    supplied X N := by
  intro u
  have bad (h : Startup.result p X.frame X.limit = .reject) :
      ∃ bits sg T, Prefix u bits ∧ Model X bits sg False T := by
    obtain ⟨T,m⟩ := invalid_startup X h
    exact ⟨[],none,T,prefix_nil u,m⟩
  by_cases safe : X.frame.elapsed ≤ X.limit
  · cases frame : X.frame with
    | live word regs elapsed =>
      have ok : elapsed ≤ X.limit := by simpa only [frame,Frame.elapsed] using safe
      by_cases valid : word.val < p
      · let pc : Fin p := ⟨word.val,valid⟩
        have eq : packed w pc.val = word := Fin.ext (packed_val word.isLt)
        exact supplied_live X hm emit u ⟨pc,regs⟩ elapsed (by simpa only [eq] using frame) ok
      · apply Or.inl (bad ?_)
        simp [Startup.result,frame,Frame.elapsed,ok,(TeamLocalClockPC.lookup_reject_iff ..).mpr (Nat.le_of_not_gt valid)]
    | accepted elapsed =>
      have ok : elapsed ≤ X.limit := by simpa only [frame,Frame.elapsed] using safe
      have cert : Endpoint X N [] (.accepted elapsed) := by
        unfold Endpoint; rw [frame]; exact ⟨rfl,ok,rfl⟩
      exact Or.inr ⟨[],.accepted elapsed,prefix_nil _,cert,emit [] _ cert⟩
  · apply Or.inl (bad ?_)
    simp [Startup.result,safe]

end TeamSite.TimedProcessor.Row

end BorderVNP
end Computability
end OAI
