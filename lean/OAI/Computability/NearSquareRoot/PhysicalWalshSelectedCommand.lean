import OAI.Computability.NearSquareRoot.PhysicalWalshSelectedPass
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # Effective command for Walsh on any Boolean selection mask

Only the grouped transform and the positional router appear as source parameters.
The mask scan, cursor rearrangements and their controller arithmetic have fixed
command files across all plans, record widths, and selected sets.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GatherProgram

open IntegerMultiplication Code KernelPass FixedPoint EffectiveBoundedTask CommonRegisters
  KernelEffectiveFamily GeneratorSyntax Filter

noncomputable section

/-- The mask scan, forward permutation, grouped transformation and inverse permutation. -/
def selectedCmd (router grouped : Cmd) : Cmd :=
  (leftCmd maskCmd).join (((((beginCmd.join (leftCmd router)).join middleCmd).join
    (leftCmd grouped)).join restoreCmd).join router)

theorem selectedCmd_effective {P : Type} [Primcodable P] {r g : P → Cmd}
    (hr : Effective ltr r) (hg : Effective ltr g) : Effective ltr (fun p => selectedCmd (r p) (g p)) :=
  (effective_const ltr (leftCmd maskCmd)).join (((((effective_const _ beginCmd).join (effective_left hr)).join
    (effective_const _ middleCmd)).join (effective_left hg)).join (effective_const _ restoreCmd) |>.join hr)

theorem selectedCmd_within (R : ℕ) : ∃ B, 0 < B ∧ ∀ r g : Cmd, Within R r → Within R g → Within B (selectedCmd r g) := by
  obtain ⟨B,mono,h₁,h₂,h₃,h₄⟩ := ((eventually_gt_atTop R).and ((RegisterSelect.within_eventually (leftCmd maskCmd)).and
    ((RegisterSelect.within_eventually beginCmd).and ((RegisterSelect.within_eventually middleCmd).and
      (RegisterSelect.within_eventually restoreCmd))))).exists
  refine ⟨B,by omega,fun r g hr hg => ?_⟩
  have r' := RegisterSelect.within_mono mono.le _ hr
  have g' := RegisterSelect.within_mono mono.le _ hg
  exact ⟨h₁,⟨⟨⟨⟨⟨h₂,within_left (by omega) r'⟩,h₃⟩,within_left (by omega) g'⟩,h₄⟩,r'⟩⟩

/-- The numerical permutation router at the command file actually emitted. -/
def PositionRunsAt (cmd : Cmd) (ρ : ℝ) (K : ℕ := 0) :=
  EffectiveBoundedTask.Runs cmd
    (fun q : {v : PositionInput // K ≤ v.k} => Pieces.sparseTime ρ q.val.k)
    (fun q => Pieces.sparseSpace q.val.k)
    (fun q => send (Controlled.Reflections.table q.val.positions,Odd.words q.val.row))
    (fun q => send (Odd.words (q.val.row ∘ (BoxFin.bitAddress q.val.positions).symm)))

/-- Run the chosen source files on the actual gathered input and return the
rounded result to its original addresses. -/
theorem selectedTaskNamed {a W K₀ : ℕ} (hw : 0 < W) (p : Plan (a+1) W W) (router grouped : Cmd)
    {ρ : ℝ} (hr : 0 ≤ ρ) (route : PositionRunsAt router ρ K₀)
    {I : Type} (k : I → ℕ) (bits : (i : I) → Finset (Fin (k i)))
    (mask : I → List Bool) (x : (i : I) → Fin (2^k i) → Record (k i))
    (large : ∀ i, K₀ ≤ k i) (hm : ∀ i, mask i = flags (bits i))
    (inner : EffectiveBoundedTask.Runs grouped (Pieces.sparseTime ρ ∘ k) (Pieces.sparseSpace ∘ k)
      (fun i => send ((tally (k i),tally (bits i).card),Pieces.words (2^k i) (lift (gatherInput (gatherPerm (bits i)) (x i)))))
      (fun i => send (Odd.words (Pieces.result hw p (k i) (bits i).card (lift (gatherInput (gatherPerm (bits i)) (x i))))))) :
    EffectiveBoundedTask.Runs (selectedCmd router grouped) (Pieces.sparseTime ρ ∘ k) (Pieces.sparseSpace ∘ k)
      (fun i => send (mask i,Odd.words (x i))) (fun i => send (Odd.words (selectedResult hw p (bits i) (x i)))) :=
  command_contract (selectedCmd router grouped) from
    selectedTaskOfGrouped hw p hr (show PositionRuns ρ K₀ from ⟨router,route⟩) k bits mask x large hm inner.task

end
end PhysicalWalsh.GatherProgram

end NearSquareRoot
end Computability
end OAI
