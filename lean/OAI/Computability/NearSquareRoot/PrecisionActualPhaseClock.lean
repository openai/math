import OAI.Computability.NearSquareRoot.PrecisionActualPhasePass
import OAI.Computability.NearSquareRoot.WalshPadding
import OAI.Computability.NearSquareRoot.PhysicalWalshRelease

/-! # Time and visited cells of the released canonical phase pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace FixedPoint

open IntegerMultiplication Code Staff Strip BoxFin SynchronizedBlocks PhaseTable ShortFourier PhysicalWalsh
open Filter

/-- Every polynomial setup over a logarithmic address width can be charged
to a single sweep of the full array, uniformly including small widths. -/
theorem setup_le_array {I : Type} {k p : I → ℕ} (H : Dom k p) :
    ∃ C : ℕ, ∀ i, p i ≤ C * 2^(k i) := by
  obtain ⟨d,A,hA⟩ := H
  obtain ⟨L,hL⟩ := eventually_atTop.1 (WalshPadding.eventually_pow_le_two_pow_half d)
  let M := (L+1)^d+1
  refine ⟨A*M, fun i ↦ ?_⟩
  suffices h : (k i+1)^d ≤ M * 2^k i by
    simpa only [Nat.mul_assoc] using (hA i).trans (Nat.mul_le_mul_left A h)
  by_cases h : L ≤ k i + 1
  · refine (hL (k i+1) h).trans ?_
    have ex := Nat.pow_le_pow_right (by decide : 0 < 2) (show (k i+1)/2 ≤ k i by omega)
    exact ex.trans (Nat.le_mul_of_pos_left _ (by dsimp [M]; omega))
  · have p := Nat.pow_le_pow_left (show k i+1 ≤ L+1 by omega) d
    exact p.trans ((Nat.le_succ _).trans (Nat.le_mul_of_pos_right M (Nat.two_pow_pos _)))

/-- Charge a polynomial descriptor computation to one full-array pass without
changing its framed register program or its linear-space estimate. -/
theorem absorbArraySetup {I : Type} {k setup time space : I → ℕ} {input output : I → Tree}
    (poly : Dom k setup) (ht : ∀ i, 2^k i ≤ time i) (hs : ∀ i, 2^k i ≤ space i)
    (run : Space.BoundedTask (fun i ↦ setup i+time i) (fun i ↦ setup i+space i) input output) :
    Space.BoundedTask time space input output := by
  obtain ⟨A,cap⟩ := setup_le_array poly
  have cover (i : I) (b : ℕ) (hb : 2^k i ≤ b) : setup i+b+1 ≤ (A+1)*(b+1) := by
    have he := (cap i).trans (Nat.mul_le_mul_left A hb)
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_add,Nat.mul_one]
    omega
  exact run.bound (A+1) (A+1) (fun i ↦ cover i (time i) (ht i))
    (fun i ↦ cover i (space i) (hs i))

/-- A fixed finite-tape machine carries out a selected row of the generated
box phase schedule, including the numerical setup and the final output copy.
The uniform constant bounds actual transitions and distinct tape cells. -/
theorem actualBoxPhaseOnTapes {I : Type} {s : Regime I} {k stage : I → ℕ} {inverse : I → Bool}
    (scale : Dom k s.scale) (K : Realizes s k) (F : s.Has inverse) (T : Realizes s stage)
    (hb : ∀ i, BoxShape.Valid (k i) (BoxScale.width (k i)) (CoprimeBox.box (k i)))
    (hd : ∀ i, 4 ≤ (CoprimeBox.box (k i)).length)
    (x : (i : I) → Fin (2^k i) → Record (k i)) (hk : ∀ i, 1 ≤ k i)
    (hx : ∀ i, ‖recordArray (x i)‖ ≤ (2:ℝ)^(13*k i)) :
    ∃ (out : (i : I) → Fin (2^k i) → Record (k i))
      (hu : ∀ i z, ‖blockCoefficient (hb i) (hd i) (scheduledBlockPhase (hb i) (inverse i) (stage i)) z‖ = 1)
      (C : ℕ),
      TapeRun (fun i ↦ C*((2^k i+1)*GridTask.recordCost (k i)+1))
        (fun i ↦ C*((2^k i+1)*(k i+1)+1))
        (fun i ↦ .fork (s.header i) (send (List.ofFn fun z ↦ Dusk.mark (x i z))))
        (fun i ↦ .fork (s.header i) (send (List.ofFn fun z ↦ Dusk.mark (out i z)))) ∧
      ∀ i, ‖recordArray (out i) - phaseLayerIsometry
        (blockCoefficient (hb i) (hd i) (scheduledBlockPhase (hb i) (inverse i) (stage i)))
        (hu i) (recordArray (x i))‖ ≤ 1/(2:ℝ)^(50*k i) := by
  obtain ⟨setup,out,hu,poly,run,err⟩ := actualBoxPhasePass K F T hb hd x hk hx
  let time i := (2^k i+1)*GridTask.recordCost (k i)
  let space i := (2^k i+1)*(k i+1)
  have dom i : space i ≤ time i := by
    apply Nat.mul_le_mul_left
    unfold GridTask.recordCost
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hspace i : 2^k i ≤ space i := by
    exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have bounded := absorbArraySetup (poly.sub scale)
    (fun i ↦ (hspace i).trans (dom i)) hspace run
  obtain ⟨C,tape⟩ := bounded.releaseOfSpaceLeTime dom
  exact ⟨out,hu,C,tape,err⟩

end FixedPoint

end

end NearSquareRoot
end Computability
end OAI
