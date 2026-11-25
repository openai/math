import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalCorrectionCanonical
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelected
import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyPayload
import OAI.Computability.NearSquareRoot.InterchangeROMStageVolume

/-! # Execution of the selected correction instruction on its two packed banks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Selected

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port Space
  InterchangeROMAddress InterchangeROM Interchange.Template

def correctFactor (C E H : ℕ) (x : Data) :=
  2*Correction.nativeFactor C E H x.b x.a x.modulusIndex x.labels (checks x) x.m x.repair

theorem computable_correctFactor (C E H : ℕ) : Computable (correctFactor C E H) :=
  Primrec.nat_mul.to_comp.comp (Computable.const 2) (Correction.computable_nativeFactor C E H
    (Data.primrec_header 1).to_comp (Data.primrec_header 3).to_comp Data.primrec_modulusIndex.to_comp
    (Data.primrec_header 4).to_comp ((Raw.primrec_checkCount.comp (Data.primrec_header 2)).to_comp)
    (Data.primrec_header 2).to_comp Data.primrec_repair.to_comp)

/-- On the actual selected instruction, the compact header is preserved and
both packed check banks receive their tag-dependent Hermite matrices. -/
theorem correct_transition :
    ∃ C E H : ℕ, ∀ (x : Data) [Fact (x.modulusIndex+1).Prime] [NeZero x.b]
      {j threshold : ℕ} (_ : Data.Valid j threshold x) (P G S : Tape)
      (_ : ∀ k ∈ P ++ G ++ S, 2 ≤ k ∧ k ≤ x.b) (f : ℕ) {D : Type}
      (pay : Series D) (width : ℕ) (_ : pay.count ≤ width)
      (u v : x.Short P G S f D) (env : Env),
      let h := send (header f P G S)
      let rows := SweepBank.layout P G S x.a x.m x.b f
      let price := correctFactor C E H x * InterchangeROMStageVolume.mass h rows.count width
      let op := applyTag x.spec (flags ∘ Prod.fst)
      SweepBank.Run env (commands x .correct)
        (packet h (SweepBank.packed rows pay u ++ SweepBank.packed rows pay v))
        (packet h (SweepBank.packed rows pay (op false u v) ++ SweepBank.packed rows pay (op true u v)))
        ⟨price,price,price⟩ := by
  obtain ⟨C,E,H,run⟩ := Correction.packed_bounded
  refine ⟨C,E,H,?_⟩
  intro x prime nz j threshold valid P G S ok f D pay width hw u v env h rows price op d base hd
  have hm : 2 ≤ x.m := valid.1.2.2.2.2.2.1
  have out := run (w:=Raw.rowCount x.m) (Data.radix_gt_one valid) (by omega : 0 < x.m)
    P G S ok x.repair pay width hw u v env d base hd
  let K := Correction.nativeFactor C E H x.b x.a x.modulusIndex x.labels (checks x) x.m x.repair
  let M := rows.count*(width+1)+1
  have hM : M ≤ InterchangeROMStageVolume.mass h rows.count width := by
    unfold M InterchangeROMStageVolume.mass
    omega
  have charge : 2*(K*M) ≤ price := by
    change _ ≤ 2*K*_
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left K hM)
  have child : K*M ≤ price := (by omega : K*M ≤ 2*(K*M)).trans charge
  exact out.mono child (Nat.add_le_add_left charge base) child

end InterchangeROMRepair.Physical.Selected

end NearSquareRoot
end Computability
end OAI
