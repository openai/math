import OAI.Computability.NearSquareRoot.PrecisionActualBlockPhase
import OAI.Computability.NearSquareRoot.PrecisionBoxPhaseInputs
import OAI.Computability.NearSquareRoot.PrecisionDirectedSlot
import OAI.Computability.NearSquareRoot.PrecisionGridPreparedPass

/-! # Execution of a generated synchronized phase row on the canonical full array -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace FixedPoint

open IntegerMultiplication Code Staff Strip BoxFin SynchronizedBlocks PhaseTable ShortFourier
  ShortFourier.BatchWord

/-- The diagonal read from this block and row of the generated physical
schedule, including missing block actions and the global direction bit. -/
def scheduledBlockPhase {k : ℕ} (h : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k))
    (inverse : Bool) (stage : ℕ) (j : Fin ((CoprimeBox.box k).length/4))
    (x : BlockAddress (BoxAxis (CoprimeBox.box k)) j) : ℂ :=
  let query := directedQuery (directedPlan (inverse,tally k)) stage j.val
  adjointValue query.1 (query.2.elim 1 (fun z ↦ actualBlockPhase h j (70*guardedK k+3) z x))

theorem scheduledBlockPhase_unit {k : ℕ} (h : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k))
    (inverse : Bool) (stage : ℕ) (j : Fin ((CoprimeBox.box k).length/4))
    (x : BlockAddress (BoxAxis (CoprimeBox.box k)) j) :
    ‖scheduledBlockPhase h inverse stage j x‖ = 1 := by
  unfold scheduledBlockPhase
  obtain ⟨b,o⟩ := directedQuery (directedPlan (inverse,tally k)) stage j.val
  cases b <;> cases o <;> simp [adjointValue, actualBlockPhase_unit]

attribute [local irreducible] componentBits fractionBits guardedK Prepared Nat.clog

/-- One framed program computes the chosen row of the forward or inverse
canonical box schedule, builds every local coefficient and its tensor
products, and applies this diagonal to the full fixed-point array. The only
setup inputs are the address width, direction and stage. -/
theorem actualBoxPhasePass {I : Type} {s : Regime I} {k stage : I → ℕ} {inverse : I → Bool}
    (K : Realizes s k) (F : s.Has inverse) (T : Realizes s stage)
    (hb : ∀ i, BoxShape.Valid (k i) (BoxScale.width (k i)) (CoprimeBox.box (k i)))
    (hd : ∀ i, 4 ≤ (CoprimeBox.box (k i)).length)
    (x : (i : I) → Fin (2^k i) → Record (k i)) (hk : ∀ i, 1 ≤ k i)
    (hx : ∀ i, ‖recordArray (x i)‖ ≤ (2:ℝ)^(13*k i)) :
    ∃ (setup : I → ℕ) (out : (i : I) → Fin (2^k i) → Record (k i))
      (hu : ∀ i z, ‖blockCoefficient (hb i) (hd i) (scheduledBlockPhase (hb i) (inverse i) (stage i)) z‖ = 1),
      Dom s.scale setup ∧
      Space.BoundedTask (fun i ↦ setup i+(2^k i+1)*GridTask.recordCost (k i))
        (fun i ↦ setup i+(2^k i+1)*(k i+1))
        (fun i ↦ .fork (s.header i) (send (List.ofFn fun z ↦ Dusk.mark (x i z))))
        (fun i ↦ .fork (s.header i) (send (List.ofFn fun z ↦ Dusk.mark (out i z)))) ∧
      ∀ i, ‖recordArray (out i) - phaseLayerIsometry
        (blockCoefficient (hb i) (hd i) (scheduledBlockPhase (hb i) (inverse i) (stage i)))
        (hu i) (recordArray (x i))‖ ≤ 1/(2:ℝ)^(50*k i) := by
  let b i := CoprimeBox.box (k i)
  let d i := (b i).length/4
  have H := generatedBoxHeader K
  have D : Realizes s d := blockCountAvailable H
  let n (i : Across d) := blockRadix (b i.1) i.2
  have N : Realizes (signal d D) n := blockRadixAvailable hb H D
  apply preparedSynchronizedPhasePass s k _ b hb hd
    (fun i ↦ scheduledBlockPhase (hb i) (inverse i) (stage i))
    (fun i ↦ scheduledBlockPhase_unit (hb i) (inverse i) (stage i)) K D N _ x hk hx
  let r := signal n N
  let p (i : Across n) := 70*guardedK (k i.1.1)+3
  have K' := landing n N _ (landing d D _ K)
  have G : Realizes r (fun i : Across n ↦ guardedK (k i.1.1)) := by
    unfold guardedK
    exact ((Realizes.fix 2).times K').plus (.fix 1)
  have P : Realizes r p := ((Realizes.fix 70).times G).plus (.fix 3)
  have F' := sendRoof n N _ (sendRoof d D _ F)
  have T' := landing n N _ (landing d D _ T)
  have B := landing n N _ (floor_ d D)
  let phase (i : Across n) (z : SlotDescriptor) :=
    letI := modulus_neZero (hb i.1.1)
    actualBlockPhase (hb i.1.1) i.1.2 (p i) z ((blockAddressRank (hb i.1.1) i.1.2).symm i.2)
  apply prepareScheduledBlock (s := r) K' F' P T' B phase
  intro v V
  exact prepareActualBlockPhase (fun i : Across n ↦ hb i.1.1)
    (sendRoof n N _ (sendRoof d D _ H)) (fun i ↦ i.1.2) B v (fun i ↦ i.2) V (floor_ n N) P

end FixedPoint

end

end NearSquareRoot
end Computability
end OAI
