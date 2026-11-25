import OAI.Computability.BorderVNP.FiniteDiagonalUnitTraceSplit

/-! # Reindexing positive-tag wide-boot native traces onto their evaluation-body returns

Every bounded body return extends to the unique accepted full trace on the true
initialized RAM, with the original chronological choices and final registers.
Only the actual startup, broadcast and two dispatch ticks are deducted.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM TeamContraction RoutingISA RoutingISA.Pins RoutingISA.Evaluator
open private within_prefix from OAI.Computability.BorderVNP.DiagonalNativeEvalStartup

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
  {boot eval : Code} {bank mem pre post after hs b mb}

private def enterBody (f : BroadcastFrame) (startup : Runs pub mac boot bank mem pre post after)
    (header : Runs pub mac readBroadcast post after hs b mb) (stable : f.Stable (readings b))
    (positive : (mb f.dst).val ≠ 0) (x : Returns eval pub mac (Function.update b 10 (mb f.dst)) mb) :
    Returns (dispatchTable boot eval) pub mac bank mem := by
  have branch : Runs pub mac (select eval) b mb (dispatchEvents f mb x.val.1) x.val.2.1 x.val.2.2 :=
    (select_iff f eval b mb stable).mpr ⟨_,rfl,by simpa only [positive,ite_false] using x.property⟩
  exact ⟨(pre++(hs++dispatchEvents f mb x.val.1),x.val.2),startup.seq (header.seq branch)⟩

private noncomputable def bodyReturnsEquiv (f : BroadcastFrame) (startup : Runs pub mac boot bank mem pre post after)
    (det : boot.deterministic = true) (header : Runs pub mac readBroadcast post after hs b mb)
    (stable : f.Stable (readings b)) (positive : (mb f.dst).val ≠ 0) :
    Returns eval pub mac (Function.update b 10 (mb f.dst)) mb ≃ Returns (dispatchTable boot eval) pub mac bank mem := by
  apply Equiv.ofBijective (enterBody f startup header stable positive)
  constructor
  · intro x y h
    have e := congrArg Subtype.val h
    change (pre++(hs++dispatchEvents f mb x.val.1),x.val.2) =
      (pre++(hs++dispatchEvents f mb y.val.1),y.val.2) at e
    obtain ⟨events,state⟩ := Prod.mk.inj e
    exact Subtype.ext (Prod.ext (by simpa [dispatchEvents] using events) state)
  · rintro ⟨⟨es,z,mz⟩,r⟩
    obtain ⟨_,_,_,_,rfl,first,next⟩ := Runs.seq_iff.mp r
    obtain ⟨rfl,rfl,rfl⟩ := startup.unique_of_deterministic det first
    obtain ⟨_,_,_,_,rfl,bc,sel⟩ := Runs.seq_iff.mp next
    obtain ⟨rfl,rfl,rfl⟩ := header.unique_of_deterministic (by decide) bc
    obtain ⟨body,rfl,go⟩ := (select_iff f eval b mb stable).mp sel
    exact ⟨⟨(body,z,mz),by simpa only [positive,ite_false] using go⟩,rfl⟩

private theorem prefixBounds (f : BroadcastFrame) (startup : Runs pub mac boot bank mem pre post after)
    (det : boot.deterministic = true) (unsigned : boot.unsigned = true)
    (header : Runs pub mac readBroadcast post after hs b mb) :
    Within (pre.length+hs.length+2) 0 0 (dispatchPrefix f mb pre hs) ∧
    traceCost (dispatchPrefix f mb pre hs) = pre.length+hs.length+2 := by
  have cost : traceCost (dispatchPrefix f mb pre hs) = pre.length+hs.length+2 := by
    simp only [dispatchPrefix,traceCost,RAMBuckets.cost_append]
    change traceCost pre + (traceCost hs + 2) = _
    rw [startup.deterministic_cost det,header.deterministic_cost (by decide)]
    omega
  have ordinary {c : Code} {s m es t mt} (r : Runs pub mac c s m es t mt)
      (d : c.deterministic = true) (u : c.unsigned = true) (e) (he : e ∈ es) :
      e.action.extra = 0 ∧ e.choices = [] := by
    obtain ⟨p,hp⟩ := ordinary_of_deterministic r d e he
    exact ⟨by rw [hp]; rfl,(r.unsigned_events u e he).1⟩
  have unitEvents (e : TeamRAM.Event w) (he : e ∈ dispatchPrefix f mb pre hs) :
      e.action.extra = 0 ∧ e.choices = [] := by
    simp only [dispatchPrefix,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with h | h | rfl | rfl
    · exact ordinary startup det unsigned _ h
    · exact ordinary header (by decide) (by decide) _ h
    · exact ⟨rfl,rfl⟩
    · exact ⟨rfl,rfl⟩
  exact ⟨⟨cost.le,fun e he => (unitEvents e he).1.le,fun e he => by rw [(unitEvents e he).2]; rfl⟩,cost⟩

/-- Bijection from charged body returns at the actual post-broadcast memory onto full
native traces. The event equation identifies the appended trace, including every
old word and every branch choice in the private library. -/
theorem charged_positiveBodyEquiv {L : Layout} (fields : ProcessorFields L) (f : BroadcastFrame)
    (startup : Runs pub mac wideStartup bank (processorMemory fields w) pre post after)
    (header : Runs pub mac readBroadcast post after hs b mb) (stable : f.Stable (readings b))
    (positive : (mb f.dst).val ≠ 0) (he : eval.withoutAccept = true)
    (ticks burst clock : ℕ) (fits : pre.length+hs.length+2 ≤ ticks) :
    let M := processorMachine (dispatchTable wideStartup eval) pub mac bank fields
    ∃ E : {x : Returns eval pub mac (Function.update b 10 (mb f.dst)) mb //
        Within (ticks-(pre.length+hs.length+2)) burst clock x.val.1} ≃ NativePath M ticks burst clock,
      ∀ x, (E x).val = dispatchPrefix f mb pre hs ++ x.val.val.1 := by
  intro M
  let lift := bodyReturnsEquiv (eval := eval) f startup (by decide) header stable positive
  have hc := dispatchTable_withoutAccept (boot := wideStartup) (by decide) he
  let conv := lift.trans (returnAcceptEquiv (dispatchTable wideStartup eval) pub mac bank (processorMemory fields w) hc)
  have events (x : Returns eval pub mac (Function.update b 10 (mb f.dst)) mb) :
      (conv x).val.2 = dispatchPrefix f mb pre hs ++ x.val.1 := by
    change pre++(hs++dispatchEvents f mb x.val.1) = _
    simp [dispatchPrefix,dispatchEvents]
  have budgets (x : Returns eval pub mac (Function.update b 10 (mb f.dst)) mb) :
      Within (ticks-(pre.length+hs.length+2)) burst clock x.val.1 ↔
        Within ticks burst clock (conv x).val.2 := by
    rw [events]
    have hp := prefixBounds f startup (by decide) (by decide) header
    exact (within_prefix hp.1 hp.2 fits).symm
  let E := (conv.subtypeEquiv budgets).trans
    (boundedAcceptEquiv (dispatchTable wideStartup eval) pub mac bank fields ticks burst clock)
  exact ⟨E,fun x => events x.val⟩

variable {R r t d link inner n : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
  {pin : Fin d → Bool} {ext : Exterior R r link → Bool}
  {u : Fin (R+1)} {ibase hbase starbase header dst : ℕ}

/-- The full positive-tag tuple really starts its evaluator body in the unique
post-broadcast bank and memory. The reindex uses the remaining exact tick budget,
preserves every event of the body, and prepends only the true deterministic prefix. -/
theorem BootSnapshot.positiveBody (snap : BootSnapshot G u pin ext ibase hbase starbase header dst
      wideStartup pub mac bank) (he : eval.withoutAccept = true) (ticks burst clock : ℕ) :
    let f := G.transferFrame u header dst
    let fields := G.processorFields u pin ext ibase hbase starbase
    let M := processorMachine (dispatchTable wideStartup eval) pub mac bank fields
    f.Agrees (readings snap.mem) → readings snap.mem (f.addr f.partner 0) = 1 →
    traceCost snap.events + f.readTicks + 2 ≤ ticks →
    ∃ (hs : List (TeamRAM.Event w)) (b : Bank w) (mb : Memory w),
      Runs pub mac readBroadcast snap.registers snap.mem hs b mb ∧
      readings mb = f.copied (readings snap.mem) f.header ∧ f.Stable (readings b) ∧
      ∃ E : {x : Returns eval pub mac (Function.update b 10 (mb f.dst)) mb //
          Within (ticks-(snap.events.length+hs.length+2)) burst clock x.val.1} ≃ NativePath M ticks burst clock,
        ∀ x, (E x).val = dispatchPrefix f mb snap.events hs ++ x.val.val.1 := by
  intro f fields M agree positive ticksFit
  have bits := (G.broadcast_input u pin ext ibase hbase starbase header dst snap.mem snap.input snap.fit).1
  obtain ⟨hs,b,mb,go,cost,stable,copied⟩ :=
    (readBroadcast_test f pub mac _ _ snap.frame snap.fit bits).complete agree
  change readings mb = f.copied (readings snap.mem) f.header at copied
  have branch : (mb f.dst).val ≠ 0 := by
    change readings mb f.dst ≠ 0
    rw [copied,←Nat.add_zero f.dst,f.copied_at _ snap.fit.branch,positive]
    decide
  have hfit : snap.events.length+hs.length+2 ≤ ticks := by
    rw [snap.run.deterministic_cost (by decide)] at ticksFit
    rw [go.deterministic_cost (by decide)] at cost
    omega
  exact ⟨hs,b,mb,go,copied,stable,charged_positiveBodyEquiv fields f snap.run go stable branch he _ _ _ hfit⟩

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
