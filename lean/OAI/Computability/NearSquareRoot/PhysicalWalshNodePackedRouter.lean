import OAI.Computability.NearSquareRoot.PhysicalWalshNodeSwapRouter
import OAI.Computability.NearSquareRoot.PhysicalWalshSwapUpper
import OAI.Computability.NearSquareRoot.PhysicalWalshFrontClock
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeRouterRate

/-! # Packed Walsh routing with one fixed three-slot gate -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.Route
open IntegerMultiplication Code Space PhysicalWalsh KernelPass

/-- Both the short slice and the wide rectangle are actual commands. -/
theorem wholeAxes (a W : ℕ) {ρ : ℝ} (rate : 1/2 < ρ) : ∃ D e : ℕ, ∀ d, e ≤ d → ∀ i j : Fin (a+1),
    let A := a+1
    let extra s := ElementarySweep.prefixExtra A (SlotSwap.reserve D A) s + SlotSwap.wideExtra ρ A s
    FlatRun (W:=W) a (nodeScan a W d extra) (nodeArena a W d) (axisSwap i j) := by
  obtain ⟨D,e,upper⟩ := SlotSwap.upperRun a W rate
  let A := a+1
  let cut := SlotSwap.reserve D A
  let extra s := ElementarySweep.prefixExtra A cut s + SlotSwap.wideExtra ρ A s
  obtain ⟨f,h⟩ := wholeSwaps a W cut extra (SlotSwap.reserve_realizes D A (Nat.succ_pos _))
    (fun _ => min_le_left ..) (fun _ => Nat.le_add_right ..) ⟨e,fun d de i j ji =>
      (upper d de i j ji).mono (fun t => Nat.add_le_add_left (Nat.le_add_left ..) _) (fun _ => le_rfl)⟩
  exact ⟨D,f,h⟩

/-- All directed pairs use the same three-slot kernel. Its surrounding four
whole-slot exchanges are accounted for in the constant of the physical code. -/
theorem routerFromFront {a W : ℕ} {ρ : ℝ} (rate : 1/2 < ρ) (upper : ρ ≤ 1) (arity : 2 ≤ a+1)
    {target source : Fin (a+1)} (different : target ≠ source) {D₀ e₀ : ℕ}
    (front : ∀ d, e₀ ≤ d → FlatRun (W:=W) a (nodeScan a W d (FrontClock.extra (a+1) W ρ D₀)) (nodeArena a W d)
      (xor a (target,source))) :
    ∃ (e : ℕ) (extra : Shape → ℕ) (c : ℝ), 0 ≤ c ∧ (∀ d, e ≤ d → XorRuns a W (nodeScan a W d extra) (nodeArena a W d)) ∧
      ∀ s, withinWidth (a+1) s → (extra s:ℝ) ≤ localTime (a+1) ρ c (RouterClock.logWidth s.w) 0 s.level (bitVolume (a+1) s) := by
  obtain ⟨D,e,swap⟩ := wholeAxes a W rate
  let mid := FrontClock.extra (a+1) W ρ D₀
  let sweep s := ElementarySweep.prefixExtra (a+1) (SlotSwap.reserve D (a+1)) s + SlotSwap.wideExtra ρ (a+1) s
  let extra s := sweep s+mid s
  have hRate : 0 ≤ ρ := by linarith
  obtain ⟨c,hc,pays⟩ := RouterClock.combined_clock D arity hRate (B:=5505+3*(D₀:ℝ)) (by positivity)
    (front:=mid) (fun s _ => FrontClock.extra_bound W D₀ hRate upper s)
  refine ⟨max e e₀,extra,c,hc,fun d hd => ?_,pays⟩
  have fit s : PhysicalWalshContext.routeArena (coords a W) Shape.w (Header.wire (a+1)) s ≤ nodeArena a W d s := le_max_right ..
  have cost s : nodeArena a W d s ≤ nodeScan a W d extra s := Nat.le_add_right ..
  apply xorRuns_of_flat cost fit
  apply flatXorRuns cost fit target source different
  · intro i j
    exact (swap d ((le_max_left ..).trans hd) i j).mono (fun t => Nat.add_le_add_left (Nat.le_add_right ..) _) (fun _ => le_rfl)
  · exact (front d ((le_max_right ..).trans hd)).mono (fun t => Nat.add_le_add_left (Nat.le_add_left ..) _) (fun _ => le_rfl)

end PhysicalWalshNode.Route

end NearSquareRoot
end Computability
end OAI
