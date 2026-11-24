import OAI.Computability.VPVNP.LiveLinkedEvaluatorImages

/-!
# Exact tail counts from the linked first and last routers

At an interior incoming cut, a zero flag routes through the old-state gather.
At the last router, a zero flag gathers the outgoing cut and a one flag installs
the accepting sentinel. The transition then counts each literal evaluator
branch separately. All earlier reports are included in the same transcript cap.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.EvaluatorRoutes

open BurstRAM LiveStageLink PairStages LiveEvaluatorEncoding LiveEvaluatorRAM LiveConfigGather
open LiveEvaluatorRAM.Schedule (callFuel calls)
open scoped Fin.CommRing

variable (G : PairStages.Group) {M : ℕ}

/-- Geometry and clock for an entire linked evaluator group. -/
structure GeometryFit (M : ℕ) : Prop where
  prep : PrepLayout G.evaluator G.transitionPub M
  transitionClock : callFuel G.evaluator ≤ G.clockAt Stage.transition
  scratchTag : G.addr.val < (G.transitionPub 3).val ∨ (G.transitionPub 3).val+5 ≤ G.addr.val
  gatherClock : 8*G.w+67 ≤ G.clock
  oldTag : G.addr.val < (G.transitionPub 1).val ∨ (G.transitionPub 1).val+fieldWords M ≤ G.addr.val
  oldBeforeNew : (G.transitionPub 1).val+fieldWords M ≤ (G.transitionPub 2).val

/-- The physical outgoing header field or the final sentinel. The cut case
permits any raw configuration encoding, including malformed words. -/
inductive Output (m : Memory G.w) (b : Option (Code G.evaluator.extra M)) : Type
  | cut (F : EvaluatorGather.Fit G true (fieldWords M)) (bits : Fin (fieldWords M*G.w) → Bool)
      (flag : m ((Router.last.data G.g G.lit) 0).val = 0)
      (image : ArrayBitImage m (EvaluatorGather.operands G true 0) bits)
      (fresh : G.addr.val < (EvaluatorGather.operands G true 0).val ∨
        (EvaluatorGather.operands G true 0).val+fieldWords M*G.w ≤ G.addr.val)
      (hs : G.evaluator.extra+2 ≤ 2^G.w) (value : b = (format F.width hs).decode bits)
  | final (flag : m ((Router.last.data G.g G.lit) 0).val = 1)
      (zero : ∀ i : Fin (fieldWords M), m ((G.transitionPub 2).val+i.val) = 0)
      (fresh : G.addr.val < (G.transitionPub 2).val ∨ (G.transitionPub 2).val+fieldWords M ≤ G.addr.val)
      (value : b = some .accepted)

namespace Output
variable {G} {m : Memory G.w} {b : Option (Code G.evaluator.extra M)}

/-- The proposed outgoing configuration's physical memory, obtained by gathering the cut or
installing the accepting endpoint. -/
def memory (o : Output G m b) : Memory G.w := match o with
  | .cut F bits .. => gatherMemory G true F m bits
  | .final .. => putMemory G true m

/-- The linked router and worker reports for the chosen outgoing cut gather or final control
write. -/
def logs (o : Output G m b) : List (Report G.w) := match o with
  | .cut _ bits .. => gatherLogs G true bits
  | .final .. => putLogs G true

/-- Identify continuations on the prepared outgoing memory with paths before preparation,
charging the outgoing router and worker reports to the cap. -/
noncomputable def handoff (o : Output G m b) (fit : GeometryFit G M) (ht : G.tagged Stage.last m)
    (cap : List (Report G.w) → Prop) : ActualPaths G.P G.clock 0 o.memory (fun rs => cap (o.logs++rs)) ≃
      ActualPaths G.P G.clock 0 m cap := by
  cases o with
  | cut F bits flag image fresh => exact gatherHandoff G true F fit.gatherClock m bits ht flag image fresh cap
  | final flag => exact putHandoff G true fit.prep.width (by have := fit.gatherClock; omega) m ht flag cap

theorem tagged (o : Output G m b) : G.tagged Stage.transition o.memory := by
  cases o <;> exact tagged_retag ..

theorem old_image (o : Output G m b) (fit : GeometryFit G M) (c : Code G.evaluator.extra M) :
    ConfigAt o.memory (G.transitionPub 1) c ↔ ConfigAt m (G.transitionPub 1) c := by
  cases o with
  | cut F bits => exact gather_frame G F m bits fit.prep fit.oldTag (Or.inl fit.oldBeforeNew) c
  | final => exact put_frame G m fit.prep fit.oldTag (Or.inr fit.oldBeforeNew) c

theorem new_image (o : Output G m b) (fit : GeometryFit G M) (z : Code G.evaluator.extra M) :
    b = some z ↔ ConfigAt o.memory (G.transitionPub 2) z := by
  cases o with
  | cut F bits flag img fresh hs value => dsimp only [memory]; rw [value]; exact (gather_image G true F hs m bits z).symm
  | final flag zero fresh value =>
    dsimp only [memory]; rw [value, Option.some.injEq, eq_comm]; exact (put_image G m fit.prep zero fresh z).symm

end Output

/-- Counts a complete suffix from the last router with all earlier reports
included. Only the incident fields and the finite transcript budget enter. -/
theorem lastCount {h Δ S H : ℕ} (layout : LiveEvaluatorTail.Layout G.evaluator.extra M G.w Δ)
    (init : Code G.evaluator.extra M) (bits : LiveChain.TailBits h Δ) (i : Fin (2^h)) (m : Memory G.w)
    (fit : GeometryFit G M) (ht : G.tagged Stage.last m)
    (incoming : ∀ c, LiveEvaluatorTail.boundary layout init bits i.castSucc = some c ↔ ConfigAt m (G.transitionPub 1) c)
    (o : Output G m (LiveEvaluatorTail.boundary layout init bits i.succ))
    (pre : List (Report G.w)) (hcap : 11 ≤ H) (preCalls : ∀ r ∈ pre++o.logs, 1+r.probes ≤ H)
    (hcost : RAMBuckets.cost Report.probes (pre++o.logs) + (10+7*(2*(2*M+1))) + calls M ≤ S*H) :
    Nat.card (ActualPaths G.P G.clock 0 m (fun rs => withinCaps S H (pre++rs))) =
      ChainAssignments.tailCount G.evaluator layout init bits i := by
  rw [Nat.card_congr (o.handoff fit ht _).symm]
  simpa only [List.append_assoc] using G.linkedTailCount layout init bits i o.memory fit.prep fit.transitionClock
    fit.scratchTag o.tagged (fun c => (incoming c).trans (o.old_image fit c).symm) (o.new_image fit)
    (pre++o.logs) hcap preCalls hcost

/-- Complete noninitial evaluator count starting at the first router. The
incoming field is gathered, after which the outgoing bank is gathered or
initialized with the accepting state and one literal transition is checked. -/
theorem nonfirstCount {h Δ S H : ℕ} (layout : LiveEvaluatorTail.Layout G.evaluator.extra M G.w Δ)
    (init : Code G.evaluator.extra M) (bits : LiveChain.TailBits h Δ) (i : Fin (2^h)) (m : Memory G.w)
    (fit : GeometryFit G M) (ht : G.tagged Stage.firstTail m) (flag : m ((Router.firstTail.data G.g G.lit) 0).val = 0)
    (F : EvaluatorGather.Fit G false (fieldWords M)) (raw : Fin (fieldWords M*G.w) → Bool)
    (image : ArrayBitImage m (EvaluatorGather.operands G false 0) raw)
    (fresh : G.addr.val < (EvaluatorGather.operands G false 0).val ∨
      (EvaluatorGather.operands G false 0).val+fieldWords M*G.w ≤ G.addr.val)
    (value : LiveEvaluatorTail.boundary layout init bits i.castSucc = (format F.width fit.prep.states).decode raw)
    (o : Output G (gatherMemory G false F m raw) (LiveEvaluatorTail.boundary layout init bits i.succ))
    (pre : List (Report G.w)) (hcap : 11 ≤ H)
    (preCalls : ∀ r ∈ (pre++gatherLogs G false raw)++o.logs, 1+r.probes ≤ H)
    (hcost : RAMBuckets.cost Report.probes ((pre++gatherLogs G false raw)++o.logs) +
      (10+7*(2*(2*M+1))) + calls M ≤ S*H) :
    Nat.card (ActualPaths G.P G.clock 0 m (fun rs => withinCaps S H (pre++rs))) =
      ChainAssignments.tailCount G.evaluator layout init bits i := by
  rw [Nat.card_congr (gatherHandoff G false F fit.gatherClock m raw ht flag image fresh _).symm]
  simpa only [List.append_assoc] using lastCount G layout init bits i (gatherMemory G false F m raw) fit
    (tagged_retag ..) (fun c => value ▸ (gather_image G false F fit.prep.states m raw c).symm) o
    (pre++gatherLogs G false raw) hcap preCalls hcost

end LiveProgram.EvaluatorRoutes

end VPVNP
end Computability
end OAI
