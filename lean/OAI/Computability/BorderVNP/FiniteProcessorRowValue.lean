import OAI.Computability.BorderVNP.FiniteProcessorAccepted

/-! # Field values of actual passing processor rows

A typed live row produces precisely its adaptive source field product after
frame and sorting verification. A propagated halted frame contributes one.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP RAMTape BurstRAM RAMSerialization TeamSite TeamPrivateFragment TeamSiteEvents
open TeamTapeHandoff TeamLocalClock RAMTape.PublicExprMachine TeamSite.SupplyRun
open scoped BigOperators Classical

variable {Q Γ : Type} {p r k a m g n d e w : ℕ} {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
private theorem chunk_product (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w) (lib : Fin a → Macro Q Γ m g)
    (weights : Returns Q Γ F m a) (fuel : ℕ) {s z : TeamOpcode.State w p r} {c fin : Window w} {es : List (TeamRAM.Event w)}
    (chunk : Chunk (P.fetch pub (macros lib fuel)) s c es z fin) :
    pathProduct P pub lib weights fuel s es =
      (TeamContraction.pathWeight es : F) * foldEvents P pub lib fuel (eventAdjustment lib weights fuel) s es := by
  induction chunk with
  | nil => simp [pathProduct,foldEvents,TeamContraction.pathWeight]
  | @cons s c e next es z fin act adv fits cap tail ih =>
    simp only [pathProduct,foldEvents,adv,TeamContraction.pathWeight,List.map_cons,List.prod_cons,Function.comp_apply,Int.cast_mul]
    rw [event_eq P pub lib weights fuel s next e adv]
    change foldEvents P pub lib fuel (eventWeight lib weights fuel) next es = _ at ih
    rw [ih]
    unfold TeamContraction.pathWeight
    ring

omit [Fintype F] in
private theorem signed_product (es : List (TeamRAM.Event w)) (nonzero : (chunkSign (some false) es).isSome = true) :
    (if (chunkSign (some false) es).getD false then -1 else 1 : F) = (TeamContraction.pathWeight es : F) := by
  obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp nonzero
  have eq := chunkSign_value (some false) es
  change (TeamPrivateCall.sign (chunkSign (some false) es)).value = 1 * TeamContraction.pathWeight es at eq
  rw [hb,one_mul] at eq
  rw [hb,← eq]
  cases b <;> simp [TeamPrivateCall.sign,TeamRAM.Sign.value]

/-- At a live input the real field processor's accepted leaf is the original
source field product. Every private and word-probe choice is exactly that row's
choice string. The bound is the signed processor's proved clock envelope. -/
theorem live_leaf (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (weights : Returns Q Γ F m a)
    (X : Processor.Row.Context P lib n d e w) (fuel : ℕ) (s z : TeamOpcode.State w p r) (elapsed : Word w)
    (frame : X.frame = .live (packed w s.pc.val) s.reg elapsed) (safe : elapsed ≤ X.limit)
    (es : List (TeamRAM.Event w)) (fin : Window w) (live : Option (Fin p))
    (chunk : Chunk (P.fetch X.pub (macros lib fuel)) s (X.window elapsed) es z fin) (closed : Closed P X.pub z fin live)
    (guard : X.guard (Finish.frame (Endpoint.closeMode live) z.reg fin.elapsed) = true) (sorted : X.sorted es)
    (nonzero : (chunkSign (some false) es).isSome = true) :
    (chunkBits es,pathProduct P X.pub lib weights fuel s es) ∈ FieldReplay.leaves (code P lib weights)
      (FieldStack.productOutput (factor lib weights) terminal) (X.cost (Processor.Row.nativeCost w m g fuel es) es)
      (Processor.start,Fintype.equivFin F 1) (StackCompiler.labeledInput Layout.input X.raw) := by
  let delta := foldEvents P X.pub lib fuel (eventAdjustment lib weights fuel) s es
  let sg := chunkSign (some false) es
  have sc := X.windowSafe elapsed safe
  obtain ⟨t,b,_,run,_,clock⟩ := close_complete P X.pub lib weights fuel chunk live closed (some false) 1 X.initial
    (X.loopBank s elapsed) [] sc (X.loopBank_clock ..) (X.loopBank_work ..) X.space
  rw [one_mul,List.append_nil] at run
  have fc : fin.cap = X.cap := (chunk.clock sc).2.2.2.2.2.2
  have view := X.startup
  rw [frame] at view
  obtain ⟨tt,_,out,ep,_⟩ := live_block P lib weights 1 delta X.last X.fits X.pub s z X.block X.limit
    elapsed X.cap fin.block fin.global fin.elapsed safe [] (chunkBits es) [] [] (X.base ∘ Processor.endpoint)
    (by simpa only [List.append_nil,Function.comp_assoc] using view) X.payload t sg live b run (fun i => by
      rw [← fc]; exact congrFun clock i)
  rw [X.guard_frame] at guard
  change Endpoint.valid (Endpoint.closeMode live) X.last z.reg fin.elapsed ((X.base ∘ Processor.endpoint) Endpoint.Port.outgoing) = true at guard
  rw [guard] at ep
  have full := (prelude_lift P lib weights 1 X.prelude (chunkBits es)).trans (endpoint_replay P lib weights ep X.base rfl)
  have model := X.live_model fuel s z elapsed frame safe es fin live chunk closed
  rw [X.guard_frame] at model
  have leaf := accepted_leaf P lib weights X (chunkBits es) sg _ _ model ⟨guard,sorted⟩ nonzero delta (by trivial) full
  have eq : delta * (if sg.getD false then -1 else 1) = pathProduct P X.pub lib weights fuel s es := by
    rw [signed_product es nonzero,chunk_product P X.pub lib weights fuel chunk]; exact mul_comm ..
  rwa [eq] at leaf

/-- The exact accepted leaf on a propagated halt has empty tape and unit field weight. -/
theorem halted_leaf (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (weights : Returns Q Γ F m a)
    (X : Processor.Row.Context P lib n d e w) (fuel : ℕ) (elapsed : Word w)
    (frame : X.frame = .accepted elapsed) (safe : elapsed ≤ X.limit) (guard : X.guard (.accepted elapsed) = true)
    (sorted : X.sorted []) :
    ([],(1:F)) ∈ FieldReplay.leaves (code P lib weights) (FieldStack.productOutput (factor lib weights) terminal)
      (X.cost (Processor.Row.nativeCost w m g fuel []) []) (Processor.start,Fintype.equivFin F 1) (StackCompiler.labeledInput Layout.input X.raw) := by
  have pre := prelude_lift P lib weights 1 X.prelude []
  have start := X.startup
  rw [frame] at start
  obtain ⟨_,_,ep⟩ := FieldProcessor.predecessor_run P lib weights 1 X.last X.fits X.pub (.accepted elapsed)
    X.block X.limit X.cap [] [] (X.base ∘ Processor.endpoint) (by simpa only [List.append_nil,Function.comp_assoc] using start)
  simp only [Startup.result,Frame.elapsed,safe,ite_true,Endpoint.afterStartup] at ep
  have full := pre.trans (endpoint_replay P lib weights ep X.base rfl)
  have cert : EndpointRow P X.pub (macros lib fuel) X.block X.limit X.cap X.frame [] (.accepted elapsed) := by
    rw [frame]; exact ⟨rfl,safe,rfl⟩
  have model := X.forward fuel [] (.accepted elapsed) cert
  have leaf := accepted_leaf P lib weights X [] (some false) _ _ model ⟨guard,sorted⟩ rfl 1 (by trivial) full
  simpa using leaf

end FieldProcessor

end BorderVNP
end Computability
end OAI
