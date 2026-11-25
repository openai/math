import OAI.Computability.BorderVNP.DiagonalNativeUnitStartup
import OAI.Computability.BorderVNP.DiagonalNativeEvaluate

/-! # Dispatch of the physically initialized evaluator on either common tag

All setup, header and dispatch instructions are deterministic and unsigned. They
consume actual ticks, but no burst words or private choices. The accepted histories
of the whole table are therefore the selected branch histories at the remaining clock.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP BurstRAM TeamContraction Pins
open scoped BigOperators Classical
open private linked_iff withoutAccept noBurst positiveWeight from OAI.Computability.BorderVNP.DiagonalNativeUnitStartup

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- The chronological startup and broadcast events before the selected body starts. -/
def dispatchPrefix (f : BroadcastFrame) (mb : Memory w) (pre broadcast : List (TeamRAM.Event w)) :
    List (TeamRAM.Event w) := pre ++ (broadcast ++ [branchRead f.dst mb,tick w])

variable (f : BroadcastFrame) (eval : Code)
    {s m pre u mu hs b mb}
    (start : Runs pub mac unitStartup s m pre u mu)
    (header : Runs pub mac readBroadcast u mu hs b mb)
    (stable : f.Stable (readings b))

private def enterStartup
    (x : Returns (selected f eval mb) pub mac (Function.update b 10 (mb f.dst)) mb) :
    Returns (withStartup eval) pub mac s m := by
  let branch : Runs pub mac (select eval) b mb (dispatchEvents f mb x.val.1) x.val.2.1 x.val.2.2 :=
    (select_iff f eval b mb stable).mpr ⟨_,rfl,x.property⟩
  exact ⟨(pre ++ (hs ++ dispatchEvents f mb x.val.1),x.val.2),linked_iff.mpr (start.seq (header.seq branch))⟩

/-- Every full evaluator return traverses the uniquely completed prefix, and every
selected-body return extends to the entire actual assembled opcode table. -/
noncomputable def startupReturnEquiv :
    Returns (selected f eval mb) pub mac (Function.update b 10 (mb f.dst)) mb ≃
      Returns (withStartup eval) pub mac s m := by
  refine Equiv.ofBijective (enterStartup f eval start header stable) ⟨?_,?_⟩
  · intro x y h
    have e := congrArg Subtype.val h
    change (pre ++ (hs ++ dispatchEvents f mb x.val.1),x.val.2) =
      (pre ++ (hs ++ dispatchEvents f mb y.val.1),y.val.2) at e
    obtain ⟨events,state⟩ := Prod.mk.inj e
    exact Subtype.ext (Prod.ext (by simpa [dispatchEvents] using events) state)
  · rintro ⟨⟨es,z,mz⟩,r⟩
    obtain ⟨b',m',fs,tail,rfl,first,next⟩ := Runs.seq_iff.mp (linked_iff.mp r)
    obtain ⟨rfl,rfl,rfl⟩ := start.unique_of_deterministic (by decide) first
    obtain ⟨u',mu',gs,body,rfl,bc,sel⟩ := Runs.seq_iff.mp next
    obtain ⟨rfl,rfl,rfl⟩ := header.unique_of_deterministic (by decide) bc
    obtain ⟨fs,rfl,go⟩ := (select_iff f eval b mb stable).mp sel
    exact ⟨⟨(fs,z,mz),go⟩,rfl⟩

/-- The exact event and post-state projections of the startup equivalence. -/
theorem startupReturnEquiv_val
    (x : Returns (selected f eval mb) pub mac (Function.update b 10 (mb f.dst)) mb) :
    (startupReturnEquiv f eval start header stable x).val =
      (dispatchPrefix f mb pre hs ++ x.val.1,x.val.2) := by
  change (pre ++ (hs ++ dispatchEvents f mb x.val.1),x.val.2) = _
  simp [dispatchPrefix,dispatchEvents]

include start header in
/-- The common startup and dispatch contributes unit sign, no bursts, no private
choices, and exactly the lengths of the two traces plus the two selector instructions. -/
theorem dispatchPrefix_effects :
    Within (pre.length+hs.length+2) 0 0 (dispatchPrefix f mb pre hs) ∧
      pathWeight (dispatchPrefix f mb pre hs) = 1 := by
  have a := start.unsigned_events (by decide)
  have h := header.unsigned_events (by decide)
  have la := start.deterministic_cost (by decide)
  have lh := header.deterministic_cost (by decide)
  have ca := noBurst la
  have ch := noBurst lh
  have complete (x : TeamRAM.Event w) (hx : x ∈ dispatchPrefix f mb pre hs) :
      x.action.extra = 0 ∧ x.choices = [] ∧ x.sign = .plus := by
    simp only [dispatchPrefix,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with first | second | rfl | rfl
    · exact ⟨ca x first,a x first⟩
    · exact ⟨ch x second,h x second⟩
    · exact ⟨rfl,rfl,rfl⟩
    · exact ⟨rfl,rfl,rfl⟩
  have cost : traceCost (dispatchPrefix f mb pre hs) = pre.length+hs.length+2 := by
    simp only [dispatchPrefix,traceCost,RAMBuckets.cost_append]
    change traceCost pre + (traceCost hs + 2) = _
    omega
  exact ⟨⟨cost.le,fun e he => (complete e he).1.le,fun e he => by rw [(complete e he).2.1]; rfl⟩,
    positiveWeight fun e he => (complete e he).2.2⟩

private theorem within_prefix {pre tail : List (TeamRAM.Event w)} {cost ticks burst clock : ℕ}
    (preBounds : Within cost 0 0 pre) (exactCost : traceCost pre = cost) (fits : cost ≤ ticks) :
    Within ticks burst clock (pre++tail) ↔ Within (ticks-cost) burst clock tail := by
  have total : traceCost (pre++tail) = cost + traceCost tail := by
    rw [← exactCost]; exact RAMBuckets.cost_append ..
  constructor
  · intro x
    refine ⟨?_,fun e he => x.length e (List.mem_append_right _ he),fun e he => x.choices e (List.mem_append_right _ he)⟩
    change traceCost tail ≤ _
    have h : traceCost (pre++tail) ≤ ticks := x.cost
    omega
  · intro x
    refine ⟨?_,fun e he => ?_,fun e he => ?_⟩
    · change traceCost (pre++tail) ≤ _
      have h : traceCost tail ≤ ticks-cost := x.cost
      omega
    · exact (List.mem_append.mp he).elim (fun h => (preBounds.length e h).trans (Nat.zero_le _)) (x.length e)
    · exact (List.mem_append.mp he).elim (fun h => (preBounds.choices e h).trans (Nat.zero_le _)) (x.choices e)

/-- At the real processor-memory initialization, removing the startup prefix gives
exactly the budgeted selected-body paths, including at a cutoff strictly below the
longest body trace. -/
noncomputable def chargedStartupEquiv {L : Layout} (fields : ProcessorFields L)
    (initial : m = processorMemory fields w) (he : eval.withoutAccept = true)
    (ticks burst clock : ℕ) (fits : pre.length+hs.length+2 ≤ ticks) :
    {x : Returns (selected f eval mb) pub mac (Function.update b 10 (mb f.dst)) mb //
      Within (ticks-(pre.length+hs.length+2)) burst clock x.val.1} ≃
      NativePath (processorMachine (withStartup eval) pub mac s fields) ticks burst clock := by
  subst m
  let E := (startupReturnEquiv f eval start header stable).trans
    (returnAcceptEquiv (withStartup eval) pub mac s (processorMemory fields w) (withoutAccept he))
  apply Equiv.trans _ (boundedAcceptEquiv (withStartup eval) pub mac s fields ticks burst clock)
  apply E.subtypeEquiv
  intro x
  change _ ↔ Within ticks burst clock ((startupReturnEquiv f eval start header stable) x).val.1
  rw [startupReturnEquiv_val]
  apply Iff.symm
  apply within_prefix (dispatchPrefix_effects f start header).1 _ fits
  simp only [dispatchPrefix,traceCost,RAMBuckets.cost_append]
  change traceCost pre + (traceCost hs + 2) = _
  rw [start.deterministic_cost (by decide),header.deterministic_cost (by decide)]
  omega

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
