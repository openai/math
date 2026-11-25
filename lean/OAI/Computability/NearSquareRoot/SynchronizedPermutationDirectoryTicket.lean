import OAI.Computability.NearSquareRoot.SynchronizedPermutationDirectory
import OAI.Computability.NearSquareRoot.CRTControlledReserveRun

/-! # Preparing the permutation directory from a chronological stage ticket -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord.PermDirectory

open IntegerMultiplication Code Strip FixedLayerTickets NearSquareRoot.Space

/-- The ticket retains the physical width, transform direction and matrix-list index. -/
def forTicket (t : Ticket) := directory (t.2.2.1,t.2.1,t.2.2.2)

theorem forTicket_poly : Poly forTicket :=
  (show Easy (fun t : Ticket => (t.2.2.1,t.2.1,t.2.2.2)) by fun_prop).poly.compose directory_poly

@[simp] theorem forTicket_header (dir : Bool) (k s : Tally) :
    forTicket (header ((dir,k),s)) = directory (dir,k,s) := rfl

theorem ticket_available {I : Type} {r : Regime I} {t : I → Ticket} (T : r.Has t) :
    r.Has (fun i => forTicket (t i)) := T.thenDo forTicket_poly

/-- An arbitrary stage ticket already available at polynomial cost in the
record width yields the complete directory with a linear-volume time and
visited-cell allowance. -/
theorem ticket_bounded {I : Type} {r : Regime I} {t : I → Ticket} {k V : I → ℕ}
    (T : r.Has t) (scale : ∀ i, r.scale i ≤ k i) (room : ∀ i, 2^(k i) ≤ V i) :
    BoundedTask V V r.header (fun i => send (forTicket (t i))) :=
  Controlled.boundedOfCarries ((ticket_available T).cooked (Controlled.ReserveStage.ripeOfWidth scale room))

/-- A valid chronological matrix index, with its actual query stored in unary. -/
abbrev ValidStage := (u : Bool × ℕ) × Fin (directedPlan (u.1,tally u.2)).length

def stageKey (u : ValidStage) : Key × Tally := ((u.1.1,tally u.1.2),tally u.2.val)

theorem stageKey_gauge : Dom (fun u : ValidStage => u.1.2) (fun u => size (stageKey u)) := by
  let w (u : ValidStage) := u.1.2
  have base : Dom w (fun u => size (u.1.1,tally u.1.2)) :=
    ⟨1,3,fun u => by simp [size_prod,size_tally,size_bit,w];omega⟩
  have plan := (directedPlan_poly.on base).length base
  have idx : Dom w (fun u : ValidStage => u.2.val) := plan.mono (fun u =>
    u.2.isLt.le.trans (Code.duration _).le)
  apply (((Dom.const w 2).mul ((Dom.base w).add idx)).add (Dom.const w 5)).mono
  intro u
  simp [stageKey,w,size_prod,size_bit,size_tally]
  omega

/-- The directory of an actual ticket is computed by one finite multitape
machine, with time and visited cells polynomial in the address width alone. -/
theorem stage_machine : PolyTreeMachine (fun u : ValidStage => u.1.2)
    (fun u => send (header (stageKey u)))
    (fun u => send (directory (u.1.1,tally u.1.2,tally u.2.val))) := by
  have g := (header_poly.on stageKey_gauge).length stageKey_gauge
  exact polyTreeMachine_of_BT (forTicket_poly.on g) g

/-- The same literal ticket admits linear time and space in the number of full
array records, uniformly over all valid matrix indices and both directions. -/
theorem stage_bounded :
    let sizeOfArray := fun u : ValidStage => 2^u.1.2
    BoundedTask sizeOfArray sizeOfArray (fun u => send (header (stageKey u)))
      (fun u => send (directory (u.1.1,tally u.1.2,tally u.2.val))) := by
  let R : Regime ValidStage := ⟨fun u => u.1.2,fun u => send (header (stageKey u)),
    (header_poly.on stageKey_gauge).length stageKey_gauge⟩
  have T : R.Has (fun u : ValidStage => header (stageKey u)) := R.self
  exact ticket_bounded T (fun _ => Nat.le_refl _) (fun _ => Nat.le_refl _)

end ShortFourier.BatchWord.PermDirectory

end NearSquareRoot
end Computability
end OAI
