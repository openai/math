import OAI.Computability.NearSquareRoot.SynchronizedPermutationUniversal
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepPhysical
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetMask

/-! # Uniform physical batch sweep with the reserve degree selected after compilation -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.PackedBatchHeader.PassPoint
open IntegerMultiplication Code Strip Adic Packed Loom Controlled BoxFin Space
open SynchronizedPermutationBudget ShortFourier.BatchWord Controlled.PositionProgram

def high (x : PassPoint) := highBits x.D x.k x.batch.val x.depth.val
def count (x : PassPoint) := live x.k x.batch.val x.depth.val
def suffix (x : PassPoint) := payloadBits x.D x.k

private theorem layout (x : PassPoint) {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) :
    let chunk := (x.count+1)*guardWidth x.k
    2*((chunk:ℝ)+1)^ρ ≤ rowFactor x.k ρ ∧ rowFactor x.k ρ ≤ 2^x.high ∧
      (3*cap x.count (guardWidth x.k-1) 0+1)*(32*x.count) ≤ 2^Packed.width (guardWidth x.k-1) 0 := by
  let w := physicalWidth (box:=CoprimeBox.box x.k)
  let active := FieldDirectory.selectBlock x.k x.batch.val x.depth.val w
  let selected := Finset.univ.image active
  have c : selected.card=x.count := by
    rw [Finset.card_image_of_injective _ active.injective,Finset.card_univ,Fintype.card_fin]
    rfl
  have hk : 1 ≤ x.k := by have := x.budget.fits; unfold SynchronizedPermutationBudget.width at this; omega
  have H := x.budget.mask_layout hk x.batch.val selected
    (FieldDirectory.selectBlock_subset x.k x.batch.val x.depth.val w) h₀ h₁ 1
  dsimp only at H
  rw [c] at H
  exact ⟨H.2.2.2.1,H.2.2.2.2.1,H.2.2.2.2.2⟩

theorem sparse (x : PassPoint) :
    (3*cap x.count (guardWidth x.k-1) 0+1)*(32*x.count) ≤ 2^Packed.width (guardWidth x.k-1) 0 :=
  (layout x (ρ:=1) (by norm_num) (by norm_num)).2.2

theorem rate (x : PassPoint) {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) :
    2*Spindle.modes (fun _ : Unit => cap x.count (guardWidth x.k-1) 0) (τ:=ρ) () ≤ rowFactor x.k ρ := by
  have pos : 0<guardWidth x.k := by unfold guardWidth; omega
  simpa only [Spindle.modes,cap,Packed.width,Nat.add_zero,Nat.sub_add_cancel pos,Nat.cast_add,Nat.cast_one]
    using (layout x h₀ h₁).1

theorem factor_high (x : PassPoint) {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) :
    rowFactor x.k ρ ≤ 2^x.high := (layout x h₀ h₁).2.1

variable {X : Type} (point : X → PassPoint)

abbrev fields (x : PassPoint) := physicalWidth (box:=CoprimeBox.box x.k)

noncomputable def rank (x : PassPoint) : Block 2 x.k ≃ PackedAddress Unit x.fields :=
  letI := modulus_neZero x.budget.valid
  recordAddress x.budget.valid x.long

noncomputable def network (x : PassPoint) : Equiv.Perm (PackedAddress Unit x.fields) :=
  batchStage (fun q => q.val / capacity x.k) x.fields
    (fun _ : Unit => PermDirectory.switchTable x.dir x.row.val) (x.side,x.depth.val) x.batch.val

/-- All header preparation, shape generation, readout, physical routes, mask and inverse
run on one domain containing every reserve degree. Restricting to a sufficiently large
literal degree after the program is chosen gives this clock and the true linear peak. -/
theorem nativeOn (ρ : ℝ) (lower : 1/2 < ρ) (upper : ρ ≤ 1)
    {U : X → Type} (u : (x : X) → Series (U x)) (positive : ∀ x, 0 < (u x).count)
    (v : (x : X) → PackedAddress Unit (point x).fields → U x → Bead) :
    let V x := 2^(point x).k*(u x).count
    let f x := fun a => v x ((point x).rank a)
    let g x := fun a => scatter (point x).network (v x) ((point x).rank a)
    ∃ d : ℕ, ∀ {Y : Type} (pick : Y → X), (∀ y, d ≤ (point (pick y)).D) →
      BoundedTask (fun y => V (pick y)*(positionFactor ρ (point (pick y)).k + rowFactor (point (pick y)).k ρ+1)) (V ∘ pick)
        (together (fun x => send (point x).descriptor) (cloth (fun x => line 2 (point x).k) u f) ∘ pick)
        (cloth (fun x => line 2 (point x).k) u g ∘ pick) := by
  let _ (x : X) := modulus_neZero (point x).budget.valid
  let r := regime point
  let Q := fun x => (point x).k
  have supply := available point
  have supplied : r.Has (fun x =>
      ((tally (point x).k,tally (point x).high,tally (guardWidth (point x).k-1),tally (point x).count,
        tally (point x).suffix),(point x).descriptor.2) : X → PlacedHeader) := by
    convert supply using 1
    funext x
    exact (congrArg (fun y : PlacedHeader => (y.1,(point x).descriptor.2)) (geometry (point x))).symm
  obtain ⟨d,run⟩ := physical (r:=r) Q (fun x => BoxScale.width (point x).k) (fun x => (point x).high)
    (fun x => guardWidth (point x).k) (fun x => (point x).count) (fun x => (point x).suffix) ρ lower
    (fun x => CoprimeBox.box (point x).k) (fun x => (point x).budget.valid) (fun x => (point x).long)
    (fun x => (point x).descriptor.2) (fun x => PermDirectory.switchTable (point x).dir (point x).row.val)
    (fun x q => q.val/capacity (point x).k) (fun x => ((point x).side,(point x).depth.val))
    (fun x => (point x).batch.val) supplied (fun x => (point x).realizes) (Dom.base Q)
    (fun x => (point x).sparse) u positive v
  refine ⟨d,fun pick enough => ?_⟩
  apply run pick (Q ∘ pick) (fun y => rowFactor (Q (pick y)) ρ) (fun _ => le_rfl)
  · intro y
    exact Nat.mul_le_mul_right _ (enough y)
  · intro y
    exact rate (point (pick y)) (by linarith) upper
  · intro y
    exact factor_high (point (pick y)) (by linarith) upper

end Benes.PackedBatchHeader.PassPoint

end NearSquareRoot
end Computability
end OAI
