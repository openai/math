import OAI.Computability.NearSquareRoot.SynchronizedBoxDecode
import OAI.Computability.NearSquareRoot.SynchronizedBoxPhysicalLayout

/-! # Physical forward and adjoint Fourier instructions in execution order -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open IntegerMultiplication IntegerMultiplication.Code Matrix SynchronizedBlocks
open SynchronizedLayers.ScheduleProgram

variable {k L : ℕ} {b : List (ℕ × ℕ)} [∀ i, NeZero (BoxFin.modulus b i)]

/-- The chronological word: a column vector encounters its first listed
gate first. -/
def executionPlan (p : Bool × Tally) := (directedPlan p).reverse

theorem executionPlan_poly : Poly executionPlan := directedPlan_poly.rev

theorem executionPlan_machine :
    PolyTreeMachine Prod.snd (fun p : Bool × ℕ => send (p.1,tally p.2))
      (fun p => send (executionPlan (p.1,tally p.2))) := by
  have h : Dom Prod.snd (fun p : Bool × ℕ => size (p.1,tally p.2)) :=
    ⟨1, 5, fun p => by simp [size_prod, size_tally, size_bit]; omega⟩
  exact polyTreeMachine_of_BT (executionPlan_poly.on h) h

/-- Exact logarithmic row count of the finite-tape output. -/
theorem executionPlan_length (dir : Bool) (k : ℕ) :
    (executionPlan (dir,tally k)).length = 936230400 * Nat.clog 2 k + 117074160 := by
  rw [executionPlan, List.length_reverse, directedPlan_length]
  unfold boxDepth BoxScale.width
  ring

/-- Left-to-right gate execution on column vectors produces the matrix
product of the list read in reverse order. -/
theorem chronological_mulVec {A X : Type} [Fintype A] [DecidableEq A]
    (f : X → Matrix A A ℂ) (w : List X) (x : A → ℂ) :
    w.foldl (fun v r => f r *ᵥ v) x = (w.reverse.map f).prod *ᵥ x := by
  induction w generalizing x with
  | nil => simp
  | cons r w ih =>
    simp only [List.foldl_cons, ih, List.reverse_cons, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Matrix.mulVec_mulVec]

/-- The actual tape word acts exactly on every padded input vector, for both
directions, with a fixed mixed-radix numbering for every spectator and bit. -/
theorem executionPlan_correct [∀ i, NeZero (BoxFin.modulus (CoprimeBox.box k) i)]
    (h : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k))
    (hd : 4 ≤ (CoprimeBox.box k).length) (dir : Bool) :
    let rows := executionPlan (dir,tally k)
    (∀ x, rows.foldl (fun v r => boxRow (physicalLayout h) hd r *ᵥ v) x =
      (if dir then (paddedFourier (CoprimeBox.box k))ᴴ else paddedFourier (CoprimeBox.box k)) *ᵥ x) ∧
    (∀ r ∈ rows, BoxStage hd (BoxFin.numberedBits h) (boxRow (physicalLayout h) hd r)) ∧
    rows.length = 3 * boxDepth k := by
  obtain ⟨hp,hs,hl⟩ := directedPlan_correct h hd (physicalLayout h) dir
  refine ⟨fun x => ?_, fun r hr => hs r (List.mem_reverse.mp hr), by simpa [executionPlan] using hl⟩
  rw [chronological_mulVec]
  simpa only [executionPlan, List.reverse_reverse] using congrArg (fun M : Matrix _ _ ℂ => M *ᵥ x) hp

/-- The uniform physical multiplication tree admits this Fourier circuit at every
sufficiently large address width. -/
theorem eventually_executionPlan :
    ∃ K : ℕ, ∀ k ≥ K,
      ∃ (h : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k)) (hd : 4 ≤ (CoprimeBox.box k).length),
        letI : ∀ i, NeZero (BoxFin.modulus (CoprimeBox.box k) i) := BoxFin.modulus_neZero h
        ∀ dir : Bool, let rows := executionPlan (dir,tally k)
        (∀ x, rows.foldl (fun v r => boxRow (physicalLayout h) hd r *ᵥ v) x =
          (if dir then (paddedFourier (CoprimeBox.box k))ᴴ else paddedFourier (CoprimeBox.box k)) *ᵥ x) ∧
        (∀ r ∈ rows, BoxStage hd (BoxFin.numberedBits h) (boxRow (physicalLayout h) hd r)) ∧
        rows.length = 3 * boxDepth k := by
  obtain ⟨K,hK⟩ := CoprimeBox.eventually_valid
  refine ⟨max K 1024, fun k hk => ?_⟩
  have h := hK k ((le_max_left ..).trans hk)
  have hd := four_le_length h (three_width_lt ((le_max_right ..).trans hk))
  let _ := BoxFin.modulus_neZero h
  exact ⟨h, hd, executionPlan_correct h hd⟩

end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
