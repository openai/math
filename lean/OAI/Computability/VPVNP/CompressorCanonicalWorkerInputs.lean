import OAI.Computability.VPVNP.CompressorCanonicalWorkerRows
import OAI.Computability.VPVNP.CompressorCanonicalWorkerFit
import OAI.Computability.VPVNP.CompressorPrefixLevelScale

/-!
# Canonical worker inputs on every reachable selection

The input threshold applies at once to the entire adaptive execution
tree. Each shrinking and refresh node gets the real demand vectors of
its own graph. Changing to a physical directory holding those vectors
preserves the emitted tapes at that node and on every continuation.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.CanonicalWorker

open Compression CursorBounds CursorNetwork PrefixLevelScale PairSimulation.LocalHistory Filter

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {A : Type*} [CommRing A] {f : B.Entry → A} {hf : B.IsSolution f}
variable {a g b l : ℕ} {X : State a g}

private theorem tree {P M w : ℕ}
    (perPass : ∀ {a' g' b' l' : ℕ} {Y : State a' g'} {p : StatePass A Y b' l'} (o : PassOrigin B f hf p),
      Y.positions ≤ P → Y.maxWireWidth ≤ M → Nonempty (WorkerInput o w))
    (E : StateExecution A b l X) (o : PassOrigins B f hf E) (within : Within P M E) :
    Nonempty (WorkerInputs E o w) := by
  induction E with
  | done => exact ⟨()⟩
  | more p next ih =>
    exact ⟨(perPass o.1 within.1 within.2.1).some,fun c => (ih c (o.2 c) (within.2.2 c)).some⟩

theorem eventually_inputs (factor : ℕ) (positive : 1 ≤ factor) : ∀ᶠ len : ℕ in atTop,
    ∀ {R : Type*} [CommRing R] {coeff : B.Entry → R} {sol : B.IsSolution coeff}
      {a' g' b' l' : ℕ} {Y : State a' g'} (E : StateExecution R b' l' Y) (o : PassOrigins B coeff sol E),
      Within (initialPositions factor len) len E → Nonempty (WorkerInputs E o (wordBits factor len)) := by
  filter_upwards [eventually_fit B factor positive] with len fits
  intro R _ coeff sol a' g' b' l' Y E o within
  apply tree B (P := initialPositions factor len) (M := len) _ E o within
  intro a'' g'' b'' l'' Z p origin pos mx
  obtain ⟨space,width,values⟩ := fits origin pos mx
  let G := SelectedTerms.grid origin
  have dense : origin.motifCount*G.d + origin.motifCount*(2+G.e) < 2^(wordBits factor len) := by
    rw [← Nat.mul_add]
    exact (Nat.le_add_right ..).trans_lt ((Nat.le_add_right ..).trans_lt space)
  exact ⟨input origin _ dense width values⟩

theorem eventually_execute_inputs (u : PairExponents B.growthConstant) (factor : ℕ) (hfactor : max S.laneBits 5 ≤ factor) :
    ∀ᶠ len : ℕ in atTop, ∀ {base lanes : ℕ} (labels : Fin (virtualBits factor len) ≃ Fin base ⊕ Fin lanes)
      (hD : 1 < virtualBits factor len) (hT : blockCount (u.θ : ℝ) len*S.laneBits ≤ lanes)
      (R : Type*) [CommRing R] (coeff : B.Entry → R) (sol : B.IsSolution coeff),
      let count := blockCount (u.θ : ℝ) len
      let X₀ := pairInput S labels hD
      Nonempty (WorkerInputs (B.execute coeff sol count hT X₀) (executeOrigins B coeff sol count hT X₀)
        (wordBits factor len)) := by
  filter_upwards [PrefixLevelScale.eventually_execute B u factor hfactor,eventually_inputs B factor (by omega)]
    with len bounded inputs
  intro base lanes labels hD hT R _ coeff sol count X₀
  exact inputs _ _ (bounded labels hD hT R coeff sol)

theorem ordinalTapes_eq {w : ℕ} (E : StateExecution A b l X) (origin : PassOrigins B f hf E)
    (I J : WorkerInputs E origin w) (z : E.Choices) : ordinalTapes E origin I z = ordinalTapes E origin J z := by
  induction E with
  | done => rfl
  | more p next ih =>
    rcases z with ⟨i,z⟩
    simp only [ordinalTapes,WorkerInput.termEquiv_tapes,ih i (origin.2 i) (I.2 i) (J.2 i) z]

open private collectLevels from OAI.Computability.VPVNP.CompressorExecutionLevels

private theorem byLevel {w : ℕ} (E : StateExecution A b l X) (origin : PassOrigins B f hf E)
    (W : E.MapWitnesses f) (r : ExecutionReaders E W) (I : WorkerInputs E origin w) (z : E.Choices) :
    ordinalTapes E origin I z = (collectLevels B f hf E W r origin z).map fun v =>
      List.ofFn (workerTapes v.origin w v.term) := by
  induction E with
  | done => rfl
  | more p next ih =>
    rcases z with ⟨i,z⟩
    simp only [ordinalTapes,collectLevels,List.map_cons,WorkerInput.termEquiv_tapes,
      ih i (origin.2 i) (W.2 i) (r.2 i) (I.2 i) z]

theorem execute_tapes {w lanes : ℕ} (count : ℕ) (h : count*S.laneBits ≤ lanes)
    (Y : State (S.degreeExponent 0) lanes)
    (I : WorkerInputs (B.execute f hf count h Y) (executeOrigins B f hf count h Y) w) (z : (B.execute f hf count h Y).Choices) :
    ordinalTapes (B.execute f hf count h Y) (executeOrigins B f hf count h Y) I z =
      (executeLevels B f hf count h Y z).map fun v => List.ofFn (workerTapes v.origin w v.term) :=
  byLevel B _ _ _ _ I z

end CompressorRecords.CanonicalWorker

end

end VPVNP
end Computability
end OAI
