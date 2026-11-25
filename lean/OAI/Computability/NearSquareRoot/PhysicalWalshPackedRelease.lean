import OAI.Computability.NearSquareRoot.PhysicalWalshNodePackedRouter
import OAI.Computability.NearSquareRoot.PhysicalWalshFrontDispatch
import OAI.Computability.NearSquareRoot.PhysicalWalshSparseSweep

/-! # The physical recursive Walsh sweep at every near-root exponent

The finite machine uses the actual rounded terminal, scaled and mixed record
banks, and packed interchanges. A recursive call's leading and trailing rows
may have arbitrary positive sizes. The call bound is that of the checked
kernel plan supplied to the compiler.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.PackedRelease
open IntegerMultiplication Code Space PhysicalWalsh KernelPass

/-- All local routed XOR commands and their cost on every admitted node. -/
theorem routes {a W : ℕ} (arity : 4 ≤ a) {ρ : ℝ} (rate : 1/2 < ρ) (upper : ρ ≤ 1) :
    ∃ (e : ℕ) (extra : Shape → ℕ) (c : ℝ), 0 ≤ c ∧
      (∀ d, e ≤ d → XorRuns a W (nodeScan a W d extra) (nodeArena a W d)) ∧
      ∀ s, withinWidth (a+1) s → (extra s:ℝ) ≤ localTime (a+1) ρ c (RouterClock.logWidth s.w) 0 s.level (bitVolume (a+1) s) := by
  obtain ⟨D,e,front⟩ := FrontDispatch.runs rate upper a W arity
  let pair := Interior.axes a arity
  have distinct : pair.1 ≠ pair.2 := by intro h;have := congrArg Fin.val h;change 2=1 at this;omega
  exact Route.routerFromFront rate upper (by omega) (D₀:=D) (e₀:=e) distinct front

/-- A single finite recursive program per normalized finite kernel plan.
It returns all rounded values in the original physical order and satisfies
both the recursively charged bound and the closed-form time/space envelope. -/
theorem pieceRelease {a W : ℕ} (p : Plan (a+1) W W) (hw : 0<W) (wide : 2 ≤ W) (arity : 4 ≤ a)
    {ρ : ℝ} (rate : 1/2 < ρ) (upper : ρ ≤ 1) (saving : (p.calls:ℝ)/W < ((a+1:ℕ):ℝ)^ρ) :
    ∃ (c : ℝ) (K d : ℕ), 0 ≤ c ∧
      PieceRelease hw p ρ c RouterClock.logWidth (envelopeSetup K d (fun _ => 0)) := by
  obtain ⟨D,_,ready⟩ := routedPieceRelease hw p (by omega) wide (by linarith : 0 ≤ ρ) saving
  obtain ⟨e,extra,c,hc,run,clock⟩ := routes (W:=W) arity rate upper
  let d := max e D
  obtain ⟨K,_,go⟩ := ready d (le_max_right ..)
  refine ⟨4*K+c,K,d,by positivity,?_⟩
  exact go extra (run d (le_max_left ..)) c RouterClock.logWidth (fun _ => 0) hc
    RouterClock.one_le_logWidth (fun _ => le_rfl) clock

/-- One actual output tape and its visited-cell/step bounds for the complete
chronological sweep over a sparse, contiguous set of selected address bits. -/
theorem sparseSweep {a W : ℕ} (p : Plan (a+1) W W) (hw : 0<W) (wide : 2 ≤ W) (arity : 4 ≤ a)
    {ρ : ℝ} (rate : 1/2 < ρ) (upper : ρ ≤ 1) (saving : (p.calls:ℝ)/W < ((a+1:ℕ):ℝ)^ρ)
    {I : Type} (b : I → Pieces.Root)
    (capacity : ∀ i,(b i).size (a:=a) (W:=W) ≤ 2^((b i).w+1))
    (fits : ∀ i,(b i).Feasible hw p (by omega)) {g R : ℝ} (hg : 0 < g) (hR : 0 ≤ R)
    (sparse : ∀ i,((b i).s:ℝ) ≤ g*(b i).k/Real.log (2+(b i).k))
    (width : ∀ i,((b i).w:ℝ) ≤ R*((b i).k+1)) : Pieces.SparseRun hw p ρ b := by
  obtain ⟨D,ready⟩ := Pieces.sparseRoutedSweep hw p (by omega) wide (by linarith : 0 < ρ) saving
  obtain ⟨e,extra,c,hc,run,clock⟩ := routes (W:=W) arity rate upper
  let d := max e D
  apply ready d (le_max_right ..) extra (run d (le_max_left ..)) c RouterClock.logWidth (fun _ => 0)
    hc RouterClock.one_le_logWidth (fun _ => le_rfl) clock b capacity fits
    (g:=g) (R:=R) (H:=R+3) (Q:=0) (q:=0) hg hR (by linarith) (by norm_num) sparse width
  · intro i;exact RouterClock.logWidth_linear_real hR (width i)
  · simp

end PhysicalWalshNode.PackedRelease

end NearSquareRoot
end Computability
end OAI
