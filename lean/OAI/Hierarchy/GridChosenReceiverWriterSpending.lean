import OAI.Hierarchy.GridChosenReceiverSpending
import OAI.Hierarchy.TraceReceiverMapExecution
import OAI.Hierarchy.TraceReceiverRegisteredTree
import OAI.Hierarchy.GridReceiverTerminalSpending

namespace OAI
/-! # Uniform bound on the terminal writer from its actual task and cache words -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.GridChosenReceiver
open ThreeFlat Diagonal PhysicalStage RAM HistoryContraction
open Computability.VPVNP.BurstRAM PrivateRAM GridRegisteredSetting TraceFactorReceiver TraceFactorReceiver.Gather
open scoped BigOperators Classical

variable {F Pins : Type} [Field F] [Fintype F] {w pc rr pp size addr fuel axes : ℕ}
variable (D : RunData F (64*w) pc rr pp size addr fuel axes (w/2)) (l : GridNativeImage.Layout)
variable (h : D.run.plan.History) (ids : List (Fin (D.roots h)))
variable {age pin suffix axes' lane : ℕ} (P : TraceReceiverForward.Source F Pins w age pin suffix ids.length axes' lane)
local notation "bank" => GridReceiverBanks.tasks w
local notation "header" => GridReceiverBanks.mapHeader w
local notation "raw" i => (fun a=>((P.seeded (i : ℕ)) a).val)
local notation "task" i => TickTerminalRoot.terminal P.arena (raw i)
local notation "phases" => (D.block.repeat D.passes).length

set_option maxHeartbeats 1200000 in
/-- At each live countdown step the cache header, the incident table and the written
port count belong to the selected registered tree. The inputs identify those real
objects, so the returned time bound is independent of the intermediate memory. -/
theorem terminal_spending (count cap commands cursor : ℕ) (width : Fin 3 → ℕ) (restored : Memory (64*w))
    (entry : P.initial=mapInput bank P.arena count cap width ids.length restored)
    (degree : l.degree=2*(2^D.block.exponent 0)) (stageRate : l.stageRate=fullRate D.block.stageClockRate 0)
    (rootRate : l.rootRate=TickTerminalRoot.rootFactor) (even : Even size)
    (large : max 64 D.block.stageClockRate≤w) (levels : phases≤w)
    (resources : ∀ i,(D.issuedTree h i).resources≤Run.treeFee (D.block.localCoefficient*(64*w+1)^3)
      phases*D.rawCharge h i)
    (arity : ∀ i : Fin ids.length,(P.value i).pins=D.issuedPorts h ids[i])
    (network : ∀ i : Fin ids.length,HEq (P.value i).net (D.issuedTree h ids[i]).compile)
    (physical : ∀ i : Fin ids.length,TraceReceiverTerminalMap.HalfRows (D.run.terminalLayer h).state
      (D.terminalWords h) (D.terminalSite h ids[i]) (task i.val) (raw i.val) suffix) :
    rebuild D l+TraceReceiverProgram.terminalClock bank P.arena count cap header commands cursor
      width P.dst P.len ids.length restored ≤ termAllowance D l h ids := by
  have paid (i : Fin ids.length) :
      7224+rootClock bank P.arena count cap header width P.dst P.len ids.length restored i +
          (perRoot+22*P.len i.val) ≤ rootBill D l h ids[i]-(visitPrice D h ids[i]+gatherPrice D h ids[i]) := by
    let node := P.O.id (P.site i)
    have cached := (P.iteration i).2.2.2
    have hits := P.index i (P.invariant i.val i.isLt.le)
    have dims := D.issued_cache_fields h ids[i] P.arena age node (P.seeded i.val) P.tag (P.value i)
      cached rfl hits (arity i) (network i)
    have root := D.joint_root_from_cache (levels:=phases) h ids[i] P.arena age node suffix (P.seeded i.val)
      P.tag (P.value i) cached rfl hits (arity i) (network i) (physical i) even large levels (resources _)
    have len : P.len i.val=(task i.val).localPins := by
      have n : P.len i.val=P.ports i := by simp [TraceReceiverForward.Source.len,TraceReceiverForward.extent,i.isLt]
      exact n.trans ((P.original i).localPins.symm.trans ((arity i).trans dims.2.symm))
    have native : rootClock bank P.arena count cap header width P.dst P.len ids.length restored i =
        TickTerminalRoot.oneCost (64*w) P.arena (task i.val) (raw i.val) := by
      unfold rootClock
      rw [←entry]
      rfl
    rw [native,len]
    unfold rootBill visitPrice gatherPrice
    simp only [degree,stageRate,rootRate]
    dsimp only at root
    omega
  have sum := Finset.sum_le_sum (s:=Finset.univ) fun i _=>paid i
  exact (Nat.add_le_add_left (terminalClock_le bank P.arena count cap header commands cursor
    width P.dst P.len ids.length restored) _).trans (by
      simpa only [termAllowance,Nat.add_assoc] using Nat.add_le_add_left sum
        (rebuild D l+(4226+TraceReceiverTasks.before_clock 0)))

end Hierarchy.GridChosenReceiver
end

end OAI
