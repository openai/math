import OAI.Hierarchy.CatalystSubstitutionTrace
import OAI.Hierarchy.CatalystSubstitutionInstall

namespace OAI
/-! # Physical substitution of a heterogeneous list of oracle occurrences

The host exposes a separate data socket for each occurrence. Each installation
hides that socket, exposes the new catalyst endpoints, and leaves every other
socket available. Exact evaluation of all remaining calls is used only for the
price proof and contributes no cells to the installed network.
-/

noncomputable section
namespace Hierarchy.CatalystSubstitution
open Catalyst ThreeFlat Routing
open scoped Classical BigOperators

variable {F : Type*} [Field F] {k p : ℕ}

/-- The full substitution lemma. One may take `G` to be the minimum of the
old gap and all occurrence gaps. The host may contain arbitrary hidden bits. -/
theorem install_gap (os : List (Occurrence F k)) (C : Host F k p (Sockets os))
    (g : (Fin p → Bool) → F) (G : ℝ)
    (old : (tableApprox C.width (exactValue os C)).Gap g G)
    (calls : ∀ o ∈ os, o.replacement.Gap o.target G) :
    (install os C).Gap g (G - 2*(k:ℝ)*(os.length:ℝ)) := by
  induction os generalizing G with
  | nil =>
    simpa [install] using (empty_cut C).gap old
  | cons o os ih =>
    have ho := (exact_cut o os C).gap old
    have hr := approxPlug_gap (cutContext o os C) o.replacement ho (calls o (by simp))
    rw [min_self] at hr
    have hnew := (approximate_cut o os C).gap hr
    have tail := ih (residual C o.replacement) (G-2*(k:ℝ)) hnew (fun a ha =>
      Approximation.Gap.mono _ (calls a (by simp [ha])) (by linarith [Nat.cast_nonneg (α:=ℝ) k]))
    apply Approximation.Gap.mono _ tail
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith

/-- The minimum includes the old gap even when the list of occurrences is empty. -/
def commonGap (D : ℝ) (d : Occurrence F k → ℝ) (os : List (Occurrence F k)) : ℝ :=
  os.foldr (fun o t => min (d o) t) D

omit [Field F] in
theorem commonGap_le_old (D : ℝ) (d : Occurrence F k → ℝ) (os : List (Occurrence F k)) :
    commonGap D d os ≤ D := by
  induction os with
  | nil => exact le_rfl
  | cons o os ih => exact (min_le_right _ _).trans ih

omit [Field F] in
theorem commonGap_le_call (D : ℝ) (d : Occurrence F k → ℝ) (os : List (Occurrence F k)) :
    ∀ o ∈ os, commonGap D d os ≤ d o := by
  induction os with
  | nil => simp
  | cons a os ih =>
    intro o ho
    rcases List.mem_cons.mp ho with rfl | ho
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih o ho)

/-- Substitution with separately specified old and occurrence gap bounds. The
initial implementation may have any cells realizing the exact contraction. -/
theorem install_gap_min (os : List (Occurrence F k)) (C : Host F k p (Sockets os))
    (A : Approximation F k p) (cut : Agrees A (tableApprox C.width (exactValue os C)))
    (g : (Fin p → Bool) → F) (D : ℝ) (d : Occurrence F k → ℝ) (old : A.Gap g D)
    (calls : ∀ o ∈ os, o.replacement.Gap o.target (d o)) :
    (install os C).Gap g (commonGap D d os - 2*(k:ℝ)*(os.length:ℝ)) :=
  install_gap os C g _ (cut.gap (Approximation.Gap.mono _ old (commonGap_le_old D d os)))
    (fun o h => Approximation.Gap.mono _ (calls o h) (commonGap_le_call D d os o h))


end Hierarchy.CatalystSubstitution

end
end OAI
