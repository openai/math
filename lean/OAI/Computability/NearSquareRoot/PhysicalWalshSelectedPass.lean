import OAI.Computability.NearSquareRoot.PhysicalWalshPositionPass
import OAI.Computability.NearSquareRoot.PhysicalWalshGatherFinite
import OAI.Computability.NearSquareRoot.PhysicalWalshGatherAccuracy
import OAI.Computability.NearSquareRoot.PhysicalWalshGatherMask

/-! # The selected Walsh pass on original ordered records

From a low-to-high Boolean selection mask, generate the gather and inverse
tables, execute the variable-depth rounded recursion and parity pass, and
restore every physical address. One machine processes all the represented
arrays in its input family. The final clock includes the output copy.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GatherProgram

open IntegerMultiplication Code Space KernelPass FixedPoint PhysicalWalshNode Filter Matrix

noncomputable section

/-- The rounded output in original address order, with the canonical
stable-gather completion determined solely by the supplied bit mask. -/
def selectedResult {a W k : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)
    (bits : Finset (Fin k)) (x : Fin (2^k) → Record k) : Fin (2^k) → Record k :=
  gatherResult hw p bits (gatherPerm bits) x

/-- Fixed scanner which turns a compact mask into its complete routing packet. -/
noncomputable def maskCmd : Cmd := GatherMask.control_volume.choose

private theorem maskRun : BoundedTask (fun m => Odd.volume m.length) (fun m => Odd.volume m.length) send
    (fun m : List Bool => send (control (m.count true) (GatherMask.perm m))) :=
  ⟨maskCmd,GatherMask.control_volume.choose_spec⟩

/-- Compile the finite-set mask and place the physically grouped command
between the two record permutations. -/
theorem selectedTaskOfGrouped {a W K₀ : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)
    {ρ : ℝ} (hr : 0 ≤ ρ) (route : PositionRuns ρ K₀)
    {I : Type} (k : I → ℕ) (bits : (i : I) → Finset (Fin (k i)))
    (mask : I → List Bool) (x : (i : I) → Fin (2^k i) → Record (k i))
    (large₀ : ∀ i, K₀ ≤ k i) (hm : ∀ i, mask i = flags (bits i))
    (grouped : BoundedTask (Pieces.sparseTime ρ ∘ k) (Pieces.sparseSpace ∘ k)
      (fun i => send ((tally (k i),tally (bits i).card),Pieces.words (2^k i) (lift (gatherInput (gatherPerm (bits i)) (x i)))))
      (fun i => send (Odd.words (Pieces.result hw p (k i) (bits i).card (lift (gatherInput (gatherPerm (bits i)) (x i))))))) :
    BoundedTask (Pieces.sparseTime ρ ∘ k) (Pieces.sparseSpace ∘ k)
      (fun i => send (mask i,Odd.words (x i))) (fun i => send (Odd.words (selectedResult hw p (bits i) (x i)))) := by
  let s i := (bits i).card
  let pos i := gatherPerm (bits i)
  let v i := lift (gatherInput (pos i) (x i))
  let y i := Pieces.result hw p (k i) (s i) (v i)
  have canonical : BoundedTask (Pieces.sparseTime ρ ∘ k) (Pieces.sparseSpace ∘ k)
      (fun i => send ((tally (k i),tally (s i)),Odd.words (x i ∘ (BoxFin.bitAddress (pos i)).symm)))
      (fun i => send (Odd.words (y i))) := by
    apply grouped.conform (fun _ => rfl) (fun _ => rfl) _ (fun _ => rfl)
    intro i; rw [lift_words]; rfl
  have tables := selectedFromTables hr route k s large₀ (fun i => by simpa [s] using (bits i).card_le_univ)
    pos x y canonical
  have generated := (maskRun.on mask).left (fun i => send (Odd.words (x i)))
  have packet i : control ((mask i).count true) (GatherMask.perm (mask i)) = control (s i) (pos i) := by
    rw [hm i]; exact (control_eq (bits i)).symm
  simp only [packet] at generated
  have chain := generated.compose tables
  apply chain.bound 1000 1000 <;> intro i
  all_goals
    have len : (mask i).length=k i := by rw [hm i]; simp [flags]
    have volume := Pieces.odd_volume_le (k i)
    have rate := Pieces.space_le_clock hr (k i)
    have row : size (Odd.words (x i)) ≤ 400*Odd.volume (k i)+1 := by
      rw [← lift_words,Pieces.words_size]; unfold Odd.volume componentBits; ring_nf; omega
  · change Odd.volume (mask i).length+Pieces.sparseTime ρ (k i)+1 ≤ _
    rw [len]; dsimp only [Function.comp_apply]; omega
  · change max (Odd.volume (mask i).length+size (Odd.words (x i))) (Pieces.sparseSpace (k i))+1 ≤ _
    rw [len]; dsimp only [Function.comp_apply]; omega

/-- The actual tape pass and its output specification for a compact mask and
an original array. Counts, position tables and zero padding are computed by
the machine. `PieceRelease` and `PositionRuns` specify the two subroutines at
their physical record boundaries. -/
theorem selectedPass {a W K₀ : ℕ} (hw : 0 < W) (p : Plan (a+1) W W) (ha : 1 < a+1)
    (correct : Correct p) {ρ c : ℝ} {L P : ℕ → ℝ} (hr : 0 < ρ) (hc : 0 ≤ c) (hP : ∀ w,0 ≤ P w)
    (release : PieceRelease hw p ρ c L P) (route : PositionRuns ρ K₀)
    {g H Q : ℝ} {q : ℕ} (hg : 0 < g) (hH : 0 ≤ H) (hQ : 0 ≤ Q) :
    ∃ K : ℕ, ∀ {I : Type} (k : I → ℕ) (bits : (i : I) → Finset (Fin (k i)))
      (mask : I → List Bool) (x : (i : I) → Fin (2^k i) → Record (k i)),
      (∀ i, K ≤ k i) → (∀ i, mask i = flags (bits i)) →
      (∀ i, ((bits i).card : ℝ) ≤ g*k i/Real.log (2+k i)) →
      (∀ i, ‖recordArray (x i)‖ ≤ (2:ℝ)^(13*k i)) →
      (∀ i, 0 ≤ L (componentBits (k i)) ∧ L (componentBits (k i)) ≤ H*(1+Real.log (2+k i))) →
      (∀ i, P (componentBits (k i)) ≤ Q*(k i+1:ℝ)^q) →
      let input i := send (mask i,Odd.words (x i))
      let output i := send (Odd.words (selectedResult hw p (bits i) (x i)))
      BoundedTask (Pieces.sparseTime ρ ∘ k) (Pieces.sparseSpace ∘ k) input output ∧
      (∃ C : ℕ, TapeRun (fun i => C*(Pieces.sparseTime ρ (k i)+1)) (fun i => C*(Pieces.sparseSpace (k i)+1)) input output) ∧
      ∀ i, ‖recordArray (selectedResult hw p (bits i) (x i)) - WithLp.toLp 2
        (BoxFin.flatWalsh (bits i) *ᵥ (fun j => FixedPoint.value (k i) (x i j)))‖ ≤ 1/(2:ℝ)^(50*k i) := by
  obtain ⟨K₁,go⟩ := Pieces.sparseGroupedPass_above hw p ha hr hc hP release (q:=q) hg hH hQ
  obtain ⟨K₂,ok⟩ := eventually_atTop.mp (eventually_accurate ha hw p correct)
  refine ⟨max (max K₁ K₂) K₀,fun {I} k bits mask x large hm sparse norm overhead setup => ?_⟩
  intro input output
  let s i := (bits i).card
  let pos i := gatherPerm (bits i)
  let v i := lift (gatherInput (pos i) (x i))
  have large₁ i : K₁ ≤ k i := (le_max_left ..).trans ((le_max_left ..).trans (large i))
  have large₂ i : K₂ ≤ k i := (le_max_right ..).trans ((le_max_left ..).trans (large i))
  have large₀ i : K₀ ≤ k i := (le_max_right ..).trans (large i)
  have guards i := ok _ (large₂ i) (bits i) (pos i) (gatherPerm_low (bits i)) (x i) (norm i)
  have grouped := go k s v large₁ sparse (fun i => (guards i).1) overhead setup
  have task := selectedTaskOfGrouped hw p hr.le route k bits mask x large₀ hm grouped.1
  exact ⟨task,task.releaseOfSpaceLeTime (fun i => Pieces.space_le_clock hr.le (k i)),fun i => (guards i).2⟩

end
end PhysicalWalsh.GatherProgram

end NearSquareRoot
end Computability
end OAI
