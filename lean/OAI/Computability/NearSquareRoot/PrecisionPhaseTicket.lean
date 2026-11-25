import OAI.Computability.NearSquareRoot.PrecisionActualPhaseClock
import OAI.Computability.NearSquareRoot.FixedLayerTickets

/-! # Framed execution from the phase ticket used by the layer interpreter -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace FixedPoint

open IntegerMultiplication Code Staff Strip BoxFin PhaseTable ShortFourier.BatchWord

/-- The kind tag of the indexed row, followed by its global width, execution
direction and matrix-list index, exactly as on the interpreter's ticket. -/
def phaseStageTicket (k : ℕ) (inverse : Bool) (stage : ℕ)
    (inside : stage < (directedPlan (inverse,tally k)).length) :
    (Bool × Bool) × Tally × Bool × Tally :=
  ((directedPlan (inverse,tally k))[stage].2.1, tally k, inverse,tally stage)

theorem phaseStageTicket_eq_header (k : ℕ) (inverse : Bool) (stage : ℕ)
    (inside : stage < (directedPlan (inverse,tally k)).length) :
    phaseStageTicket k inverse stage inside = FixedLayerTickets.header ((inverse,tally k),tally stage) :=
  (FixedLayerTickets.header_at (inverse,tally k) ⟨stage, inside⟩).symm

/-- The physical schedule indices have linear unary size in the global
address width, since the number of stages is logarithmic in that width. -/
theorem phaseStageTicket_size (k : ℕ) (inverse : Bool) (stage : ℕ)
    (inside : stage < (directedPlan (inverse,tally k)).length) :
    size (phaseStageTicket k inverse stage inside) ≤ 10000000000*(k+1) := by
  have hs := inside
  rw [directedPlan_length] at hs
  have logBound : Nat.clog 2 k ≤ k := Nat.clog_le_of_le_pow
    (Nat.lt_pow_self (n := k) (by decide : 1 < 2)).le
  unfold boxDepth BoxScale.width at hs
  simp only [phaseStageTicket,size_prod,size_bit,size_tally,tally_length]
  omega

theorem phaseStageTicket_size_le_array (k : ℕ) (inverse : Bool) (stage : ℕ)
    (inside : stage < (directedPlan (inverse,tally k)).length) :
    size (phaseStageTicket k inverse stage inside) ≤ 10000000000*(2^k+1) :=
  (phaseStageTicket_size k inverse stage inside).trans (Nat.mul_le_mul_left _
    (Nat.succ_le_succ (Nat.lt_pow_self (n := k) (by decide : 1 < 2)).le))

def phaseTicketRegime {I : Type} (k stage : I → ℕ) (inverse : I → Bool)
    (inside : ∀ i, stage i < (directedPlan (inverse i,tally (k i))).length) : Regime I where
  scale := k
  header := fun i ↦ send (phaseStageTicket (k i) (inverse i) (stage i) (inside i))
  gauge := by
    refine ⟨1,10000000000, fun i ↦ ?_⟩
    change size (phaseStageTicket (k i) (inverse i) (stage i) _) ≤ _
    simpa only [pow_one] using phaseStageTicket_size (k i) (inverse i) (stage i) (inside i)

/-- Given only the physical row ticket and a flat array, one framed program
retains the ticket and returns the phase-transformed array. All setup and
all copies are included in the stated clock and space. -/
theorem phaseTicketPass {I : Type} (k stage : I → ℕ) (inverse : I → Bool)
    (inside : ∀ i, stage i < (directedPlan (inverse i,tally (k i))).length)
    (hb : ∀ i, BoxShape.Valid (k i) (BoxScale.width (k i)) (CoprimeBox.box (k i)))
    (hd : ∀ i, 4 ≤ (CoprimeBox.box (k i)).length)
    (x : (i : I) → Fin (2^k i) → Record (k i)) (hk : ∀ i, 1 ≤ k i)
    (hx : ∀ i, ‖recordArray (x i)‖ ≤ (2:ℝ)^(13*k i)) :
    ∃ (out : (i : I) → Fin (2^k i) → Record (k i))
      (hu : ∀ i z, ‖blockCoefficient (hb i) (hd i) (scheduledBlockPhase (hb i) (inverse i) (stage i)) z‖ = 1),
      Space.BoundedTask (fun i ↦ (2^k i+1)*GridTask.recordCost (k i))
        (fun i ↦ (2^k i+1)*(k i+1))
        (fun i ↦ .fork (send (phaseStageTicket (k i) (inverse i) (stage i) (inside i)))
          (send (List.ofFn fun z ↦ Dusk.mark (x i z))))
        (fun i ↦ .fork (send (phaseStageTicket (k i) (inverse i) (stage i) (inside i)))
          (send (List.ofFn fun z ↦ Dusk.mark (out i z)))) ∧
      ∀ i, ‖recordArray (out i) - phaseLayerIsometry
        (blockCoefficient (hb i) (hd i) (scheduledBlockPhase (hb i) (inverse i) (stage i)))
        (hu i) (recordArray (x i))‖ ≤ 1/(2:ℝ)^(50*k i) := by
  let s := phaseTicketRegime k stage inverse inside
  have H : s.Has (fun i ↦ phaseStageTicket (k i) (inverse i) (stage i) (inside i)) := Regime.self
  have p := H.ez Easy.snd
  have K : Realizes s k := p.ez Easy.fst
  have F : s.Has inverse := (p.ez Easy.snd).ez Easy.fst
  have T : Realizes s stage := (p.ez Easy.snd).ez Easy.snd
  obtain ⟨setup,out,hu,poly,run,err⟩ := actualBoxPhasePass K F T hb hd x hk hx
  have budget (i : I) (c : ℕ) (h : 0 < c) : 2^k i ≤ (2^k i+1)*c :=
    (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ h)
  have complete := absorbArraySetup (k := k) poly
    (fun i ↦ budget i (GridTask.recordCost (k i)) (by unfold GridTask.recordCost; positivity))
    (fun i ↦ budget i (k i+1) (Nat.succ_pos _)) run
  exact ⟨out, hu, complete, err⟩

end FixedPoint

end

end NearSquareRoot
end Computability
end OAI
