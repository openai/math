import OAI.Computability.BorderVNP.TeamSiteProcessorRow
import OAI.Computability.BorderVNP.TeamSiteEndpointReject

/-! # From a guarded live RAM row to a complete physical processor replay -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Processor.Row

open VPVNP BurstRAM RAMTape RAMSerialization TeamPrivateFragment Layout TeamTapeHandoff TeamLocalClock
open TeamSiteChoices TeamSiteEvents SupplyRun RAMTape.PublicExprMachine

variable {Q Γ : Type} {p r k a m g n d e w : ℕ}
variable {P : TeamOpcode.Program p r k a} {lib : Fin a → Macro Q Γ m g}
variable (X : Context P lib n d e w)

/-- Clock window after successful reception of a live predecessor. -/
abbrev Context.window (elapsed : Word w) := blockWindow X.block X.limit elapsed X.cap

/-- Canonical actual register/clock installation inside the full endpoint's work bank. -/
noncomputable def Context.loopBank (s : TeamOpcode.State w p r) (elapsed : Word w) :=
  installStacks TeamSite.Port.clock (X.base ∘ site) ((X.window elapsed).bank X.pub s)

theorem Context.windowSafe (elapsed : Word w) (ok : elapsed ≤ X.limit) : (X.window elapsed).Safe := by
  unfold Window.Safe
  rw [← blockWindow_total X.block X.limit elapsed X.cap ok]
  exact X.limit.isLt

/-- Actual starting RAM clock bank at the beginning of the live row. -/
theorem Context.loopBank_clock (s : TeamOpcode.State w p r) (elapsed : Word w) :
    X.loopBank s elapsed ∘ TeamSite.Port.clock = (X.window elapsed).bank X.pub s :=
  funext fun i => installStacks_at (fun _ _ he => TeamSite.Port.clock.inj he) _ _ i

/-- Initialized chronological records and all private scratch survive the startup decoder. -/
theorem Context.loopBank_work (s : TeamOpcode.State w p r) (elapsed : Word w) :
    Work.Ready X.hw₂ (2^e) X.initial (X.loopBank s elapsed) := X.work.installClock _

/-- The physical ending-frame test on a live block is exactly the row's transmitted
candidate (or the final halt test). -/
theorem Context.guard_frame (live : Option (Fin p)) (regs : Fin r → Word w) (elapsed : Word w) :
    X.guard (Finish.frame (Endpoint.closeMode live) regs elapsed) =
      Endpoint.valid (Endpoint.closeMode live) X.last regs elapsed (X.base .outgoing) := by
  cases hl : X.last <;> cases live <;> simp [Context.guard,Endpoint.valid,hl,Endpoint.closeMode,Finish.frame,Finish.Mode.halted,Frame.halted]

/-- Time envelope of one complete physical instruction loop, including its terminal fetch. -/
abbrev nativeCost (w m g fuel : ℕ) (es : List (TeamRAM.Event w)) :=
  Work.chunkBudget w m g fuel es + Work.closeBudget w

/-- An exact guarded native chunk gives a true physical terminal. Its transmitted frame
and memory sorting tests determine whether that terminal validates the chunk. -/
theorem Context.live_model (fuel : ℕ) (s z : TeamOpcode.State w p r) (elapsed : Word w)
    (inputFrame : X.frame = .live (packed w s.pc.val) s.reg elapsed) (safe : elapsed ≤ X.limit)
    (es : List (TeamRAM.Event w)) (fin : Window w) (live : Option (Fin p))
    (chunk : Chunk (P.fetch X.pub (macros lib fuel)) s (X.window elapsed) es z fin)
    (closed : Closed P X.pub z fin live) :
    X.Model (chunkBits es) (chunkSign (some false) es)
      (X.guard (Finish.frame (Endpoint.closeMode live) z.reg fin.elapsed) = true ∧ X.sorted es)
      (X.cost (nativeCost w m g fuel es) es) := by
  let sg := chunkSign (some false) es
  let decoded := X.loopBank s elapsed
  have sc := X.windowSafe elapsed safe
  obtain ⟨t,b,ht,run,wr,cr⟩ := close_complete P X.pub lib fuel chunk live closed (some false) X.initial
    decoded [] sc (X.loopBank_clock ..) (X.loopBank_work ..) X.space
  rw [List.append_nil] at run
  have fc : fin.cap = X.cap := (chunk.clock sc).2.2.2.2.2.2
  have view := X.startup
  rw [inputFrame] at view
  obtain ⟨tt,htt,out,hfull,hsites⟩ := Endpoint.live_block P lib X.last X.fits X.pub s z X.block X.limit
    elapsed X.cap fin.block fin.global fin.elapsed safe [] (chunkBits es) [] [] (X.base ∘ endpoint)
    (by simpa only [List.append_nil,Function.comp_assoc] using view) X.payload t sg live b run (fun i => by
      rw [← fc]; exact congrFun cr i)
  have hb : RecordBuffer.Holds X.hw₂ (2^e) (X.slots es) (out ∘ Endpoint.Port.site ∘ probe ∘ TeamProbeEmit.Port.buffer) := by
    have same : out ∘ Endpoint.Port.site ∘ probe ∘ TeamProbeEmit.Port.buffer = b ∘ probe ∘ TeamProbeEmit.Port.buffer :=
      funext fun i => hsites _
    rw [same,Context.slots,inputFrame]
    exact wr.buffer
  rw [X.guard_frame]
  apply X.finish es sg _ (nativeCost w m g fuel es) _ hfull hb
  change t ≤ nativeCost w m g fuel es at ht
  nlinarith

/-- From a typed live exit certificate, recover the exact native chunk and close mode. -/
theorem Context.forward_live (fuel : ℕ) (word elapsed : Word w) (regs : Fin r → Word w)
    (inputFrame : X.frame = .live word regs elapsed) {es : List (TeamRAM.Event w)} {out : Frame w r}
    (certificate : EndpointRow P X.pub (macros lib fuel) X.block X.limit X.cap X.frame es out) :
    X.Model (chunkBits es) (chunkSign (some false) es) (X.guard out = true ∧ X.sorted es)
      (X.cost (nativeCost w m g fuel es) es) := by
  rw [inputFrame] at certificate
  obtain ⟨ok,pc,z,fin,hpc,chunk,endMode⟩ := certificate
  subst word
  let s : TeamOpcode.State w p r := ⟨pc,regs⟩
  rcases endMode with ⟨guard,rfl⟩ | ⟨guard,rfl⟩
  · exact X.live_model fuel s z elapsed inputFrame ok es fin none chunk (Or.inl ⟨rfl,congrArg Prod.fst guard⟩)
  · exact X.live_model fuel s z elapsed inputFrame ok es fin (some z.pc) chunk (Or.inr ⟨rfl,congrArg Prod.fst guard⟩)

end TeamSite.Processor.Row

end BorderVNP
end Computability
end OAI
