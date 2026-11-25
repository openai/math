import OAI.LinearAlgebra.FiniteFourier.PrimeTemplateProgram.PrimeRoutedBlocks

/-! # Gathering and scattering one charged rectangle

Source rows are first pulled to a common coordinate system, combined there, and
transformed once per work row. Target rows read the common outputs through
their own local coordinate changes.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

variable {K : Type*} [CommSemiring K]

/-- The block from a source row to a target row of one charged rectangle. -/
def chargedRectangleMatrix {S T W X Y : Type} [Fintype Y] (B : Matrix W W K)
    (post : T → Matrix X Y K) (M : Matrix Y Y K) (pre : S → Matrix Y X K) :
    Matrix ((T × W) × X) ((S × W) × X) K :=
  Matrix.of fun o i => B o.1.2 i.1.2 * (post o.1.1 * M * pre i.1.1) o.2 i.2

private theorem charged_local_rows {D X Y : Type} [Fintype D] [Fintype X] [DecidableEq D]
    {A : D → Matrix Y X K} {c : ℕ} (h : ∀ d, RealizableAtMost (A d) c) :
    RealizableAtMost (Matrix.of fun (o : D × Y) (i : D × X) => if o.1 = i.1 then A o.1 o.2 i.2 else 0)
      (Fintype.card D * c) := by
  have hb := (RealizableAtMost.blockDiagonal_family h).reindex (Equiv.prodComm Y D) (Equiv.prodComm X D)
  convert hb using 1
  · ext ⟨d, x⟩ ⟨e, y⟩
    by_cases hd : d = e <;> simp [Matrix.reindex_apply, Matrix.blockDiagonal_apply, hd]
  · simp

/-- The circuit around the middle transform uses dense row mixing only on
the fixed row indices. The coordinate dimension enters linearly. -/
theorem chargedRectangle_template_of_packed {ℓ f F : ℕ} {ζ : K} {S T W X Y : Type}
    [Fintype S] [Fintype T] [Fintype W] [Fintype X] [Fintype Y] [DecidableEq W]
    {M : Matrix Y Y K} {c s cPre cPost : ℕ}
    (B : Matrix W W K) (post : T → Matrix X Y K) (pre : S → Matrix Y X K)
    (hpost : ∀ t, RealizableAtMost (post t) cPost)
    (hpre : ∀ l, RealizableAtMost (pre l) cPre)
    (hM : PrimeTemplateProgram ℓ f F ζ (Matrix.blockDiagonal fun _ : W => M) c s) :
    PrimeTemplateProgram ℓ f F ζ (chargedRectangleMatrix B post M pre)
      (Fintype.card W * (Fintype.card S * cPre + Fintype.card T * cPost) +
        Fintype.card Y * (Fintype.card W * (Fintype.card S * Fintype.card W)) + c) s := by
  classical
  let P := Matrix.of fun (o : (S × W) × Y) (i : (S × W) × X) =>
    if o.1 = i.1 then pre o.1.1 o.2 i.2 else 0
  let Q := Matrix.of fun (o : (T × W) × X) (i : (T × W) × Y) =>
    if o.1 = i.1 then post o.1.1 o.2 i.2 else 0
  have hp : RealizableAtMost P (Fintype.card (S × W) * cPre) :=
    charged_local_rows (fun u : S × W => hpre u.1)
  have hq : RealizableAtMost Q (Fintype.card (T × W) * cPost) :=
    charged_local_rows (fun u : T × W => hpost u.1)
  let mix := Matrix.of fun (w : W) (i : S × W) => B w i.2
  let G := Matrix.of fun (o : Y × W) (i : (S × W) × Y) =>
    if o.1 = i.2 then B o.2 i.1.2 else 0
  have hg : RealizableAtMost G (Fintype.card Y * (Fintype.card W * Fintype.card (S × W))) := by
    convert ((realizableAtMost_card_mul_card mix).blockDiagonal Y).reindex
      (Equiv.prodComm W Y) (Equiv.refl _) using 1
    ext ⟨x, w⟩ ⟨⟨l, v⟩, y⟩
    simp [G, mix, Matrix.reindex_apply, Matrix.blockDiagonal_apply]
  let D := Matrix.of fun (o : (T × W) × Y) (i : Y × W) =>
    if (o.2, o.1.2) = i then (1 : K) else 0
  have hd : RealizableAtMost D 0 := by
    refine ⟨0, le_rfl, ⟨.nil, fun o => .scaled 1 (.inl (o.2, o.1.2))⟩, ?_⟩
    ext o i
    simp [D, Circuit.matrix, Circuit.eval, Readout.eval, Pi.single_apply]
  have hIn (y : Y) (u : W) (i : S × W) (x : X) :
      (G * P) (y, u) (i, x) = B u i.2 * pre i.1 y x := by
    simp [Matrix.mul_apply, Fintype.sum_prod_type, P, G, mul_ite, ite_mul, Finset.sum_ite_irrel]
  have hOut (o : T × W) (y : X) (x : Y) (u : W) :
      (Q * D) (o, y) (x, u) = if o.2 = u then post o.1 y x else 0 := by
    obtain ⟨t,w⟩ := o
    by_cases hw : w = u <;>
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Q, D, Prod.mk.injEq, mul_ite, ite_and, hw]
  have hMid (o : T × W) (y : X) (x : Y) (u : W) :
      (Q * D * Matrix.blockDiagonal (fun _ : W => M)) (o, y) (x, u) =
        if o.2 = u then (post o.1 * M) y x else 0 := by
    simp [Matrix.mul_apply, Fintype.sum_prod_type, hOut, Matrix.blockDiagonal_apply, mul_ite,
      ite_mul, Finset.sum_ite_irrel]
  have hFull : Q * D * Matrix.blockDiagonal (fun _ : W => M) * (G * P) =
      chargedRectangleMatrix B post M pre := by
    ext ⟨o, y⟩ ⟨i, x⟩
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [hMid, hIn, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      chargedRectangleMatrix, Matrix.of_apply]
    rw [Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [← hFull]
  convert ((PrimeTemplateProgram.localCircuit (hq.mul hd)).serial hM).serial
      (.localCircuit (hg.mul hp)) using 1 <;> simp [Fintype.card_prod]
  ring

/-- Each of the work rows uses the same kernel program. Its number of
calls is independent of the numbers of source and target labels. -/
theorem chargedRectangle_template {ℓ f F : ℕ} {ζ : K} {S T W X Y : Type}
    [Fintype S] [Fintype T] [Fintype W] [Fintype X] [Fintype Y]
    {M : Matrix Y Y K} {c s cPre cPost : ℕ}
    (B : Matrix W W K) (post : T → Matrix X Y K) (pre : S → Matrix Y X K)
    (hpost : ∀ t, RealizableAtMost (post t) cPost)
    (hpre : ∀ l, RealizableAtMost (pre l) cPre)
    (hM : PrimeTemplateProgram ℓ f F ζ M c s) :
    PrimeTemplateProgram ℓ f F ζ (chargedRectangleMatrix B post M pre)
      (Fintype.card W * (Fintype.card S * cPre + Fintype.card T * cPost) +
        Fintype.card Y * (Fintype.card W * (Fintype.card S * Fintype.card W)) +
        Fintype.card W * c) (Fintype.card W * s) := by
  classical
  apply chargedRectangle_template_of_packed B post pre hpost hpre
  simpa using PrimeTemplateProgram.blockDiagonal (fun _ : W => hM)

end

end

end FiniteFourier
end LinearAlgebra
end OAI
