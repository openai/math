import OAI.Hierarchy.CatalystSubstitutionFamily
import OAI.Hierarchy.CatalystSubstitutionPinned

namespace OAI
/-! # Substitution with a fixed public data word

Pinning the public word commutes with contracting a call. The oracle data
remain exposed in its own gap estimate, hence the binary selector charge
is still exactly one per occurrence, independently of the public arity.
-/

noncomputable section
namespace Hierarchy.CatalystSubstitution
open Catalyst ThreeFlat Routing LinearAlgebra.SpectralBooks
open scoped Classical BigOperators
variable {F : Type*} [Field F] {k p q : ℕ}

theorem Agrees.pointwise {A B : Approximation F k p} (h : Agrees A B)
    {g : (Fin p → Bool) → F} {D : ℝ} (old : A.PointwiseGap g D) : B.PointwiseGap g D := by
  obtain ⟨a,an⟩ := A
  obtain ⟨b,bn⟩ := B
  obtain ⟨hw,e⟩ := h
  change a = b at hw
  cases hw
  have eq : (⟨a,an⟩ : Approximation F k p).coeff = (⟨a,bn⟩ : Approximation F k p).coeff := funext e
  let test (v : (Port p a → Bool) → F) :=
    ∀ P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k)), ∀ pin : Fin p → Bool,
      let row := fun w : Wire a × Bool → Bool => (v-ideal a g) (Sum.elim pin w)
      row = 0 ∨ P.price (bitTensor row) (fun i => sites (p:=p) a (.inr i)) ≤ 2*(∑ j, (a j : ℝ))-D
  exact (congrArg test eq).mp old

private theorem pointwise_mono {A : Approximation F k p} {g : (Fin p → Bool) → F}
    {d D : ℝ} (h : A.PointwiseGap g D) (hd : d ≤ D) : A.PointwiseGap g d := by
  intro P x
  exact (h P x).imp_right (fun e => e.trans (sub_le_sub_left hd _))

private def pinContext (C : Context F k p q) (a : Fin p → Bool) : Context F k 0 q :=
  ⟨C.width,TypedWiring.localTable (fun x : Port 0 C.width ⊕ Fin q → Bool =>
    C.coeff (Sum.elim a (fun w => x (.inl (.inr w)))) (x ∘ Sum.inr))⟩

private theorem pinContext_coeff (C : Context F k p q) (a : Fin p → Bool)
    (x : Port 0 C.width → Bool) (h : Fin q → Bool) :
    (pinContext C a).coeff x h = C.coeff (Sum.elim a (x ∘ Sum.inr)) h := by
  unfold Context.coeff pinContext
  rw [TypedWiring.localTable_value]; rfl

private theorem pin_exact (C : Context F k p q) (a : Fin p → Bool) (f : (Fin q → Bool) → F) :
    Agrees (pinWord (exactPlug C f) a) (exactPlug (pinContext C a) f) := by
  refine ⟨rfl,fun x => ?_⟩
  change Port 0 C.width → Bool at x
  change (pinWord (exactPlug C f) a).coeff x = (exactPlug (pinContext C a) f).coeff x
  erw [pinWord_coeff (exactPlug C f) a x,exactPlug_coeff C f _,exactPlug_coeff (pinContext C a) f x]
  apply Finset.sum_congr (by ext h; simp)
  intro h _
  exact congrArg (fun z => z * f h) (pinContext_coeff C a x h).symm

private theorem pin_approx (C : Context F k p q) (a : Fin p → Bool) (X : Approximation F k q) :
    Agrees (approxPlug (pinContext C a) X) (pinWord (approxPlug C X) a) := by
  refine ⟨rfl,fun x => ?_⟩
  change Port 0 (fun j => C.width j + X.width j) → Bool at x
  change (approxPlug (pinContext C a) X).coeff x = (pinWord (approxPlug C X) a).coeff x
  erw [pinWord_coeff (approxPlug C X) a x,approxPlug_coeff (pinContext C a) X x,approxPlug_coeff C X _]
  have oldWord : Sum.elim a (x ∘ oldPort C.width X.width ∘ Sum.inr) =
      Sum.elim a (x ∘ Sum.inr) ∘ oldPort C.width X.width := by
    funext i; rcases i with j | ⟨w,s⟩ <;> rfl
  have newWord : x ∘ newPort C.width X.width = Sum.elim a (x ∘ Sum.inr) ∘ newPort C.width X.width := by
    funext i; rcases i with ⟨w,s⟩; rfl
  apply Finset.sum_congr (by ext h; simp)
  intro h _
  exact congrArg₂ (· * ·)
    ((pinContext_coeff C a (x ∘ oldPort C.width X.width) h).trans
      (congrArg (fun u => C.coeff u h) oldWord))
    (congrArg (fun u => X.coeff (Sum.elim h u)) newWord)

/-- A single substitution keeps all public pins fixed throughout the price proof. -/
theorem approxPlug_pointwise (C : Context F k p q) (X : Approximation F k q)
    {f : (Fin q → Bool) → F} {g : (Fin p → Bool) → F} {D d : ℝ}
    (hg : (exactPlug C f).PointwiseGap g D) (hx : X.Gap f d) :
    (approxPlug C X).PointwiseGap g (min D d - 2*(k:ℝ)) := by
  apply pointwise_of_pinWord_gap
  intro a
  have old := (pin_exact C a f).gap (pinWord_gap _ a g hg)
  exact (pin_approx C a X).gap (approxPlug_gap (pinContext C a) X old hx)

private theorem install_pointwise_at (os : List (Occurrence F k)) (C : Host F k p (Sockets os))
    (g : (Fin p → Bool) → F) (G : ℝ)
    (old : (tableApprox C.width (exactValue os C)).PointwiseGap g G)
    (calls : ∀ o ∈ os, o.replacement.Gap o.target G) :
    (install os C).PointwiseGap g (G-2*(k:ℝ)*(os.length:ℝ)) := by
  induction os generalizing G with
  | nil =>
    simpa [install] using (empty_cut C).pointwise old
  | cons o os ih =>
    have ho := (exact_cut o os C).pointwise old
    have hr := approxPlug_pointwise (cutContext o os C) o.replacement ho (calls o (by simp))
    rw [min_self] at hr
    have hnew := (approximate_cut o os C).pointwise hr
    have tail := ih (residual C o.replacement) (G-2*(k:ℝ)) hnew (fun a ha =>
      Approximation.Gap.mono _ (calls a (by simp [ha])) (by linarith [Nat.cast_nonneg (α:=ℝ) k]))
    apply pointwise_mono tail
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith

/-- All physical calls use their exposed estimates, while the old public word
is fixed independently in every retained and erroneous term. -/
theorem install_pointwise (os : List (Occurrence F k)) (C : Host F k p (Sockets os))
    (A : Approximation F k p) (cut : Agrees A (tableApprox C.width (exactValue os C)))
    (g : (Fin p → Bool) → F) (D : ℝ) (d : Occurrence F k → ℝ) (old : A.PointwiseGap g D)
    (calls : ∀ o ∈ os, o.replacement.Gap o.target (d o)) :
    (install os C).PointwiseGap g (commonGap D d os - 2*(k:ℝ)*(os.length:ℝ)) :=
  install_pointwise_at os C g _ (cut.pointwise (pointwise_mono old (commonGap_le_old D d os)))
    (fun o h => Approximation.Gap.mono _ (calls o h) (commonGap_le_call D d os o h))


end Hierarchy.CatalystSubstitution

end
end OAI
