import OAI.Computability.NearSquareRoot.InterchangePackedPencil
import OAI.Computability.NearSquareRoot.InterchangeSpectralRequest

/-!
# The full repair schedule for a group of interchange queries

The predictor is the literal grouped bank program on independent base components.
Only the two blocks of check rows enter the forward and inverse spectral sweeps.
Restricting the resulting ordinary rows to any main-coordinate fibre gives the
Hermite repair program and hence the simultaneous swap of all its main pairs.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace Interchange.RepairSchedule

open OAI.LinearAlgebra.FiniteFourier SwapSpectrum SwapRepair Matrix

variable {K C Addr L B H : Type} [Field K] {m : ℕ}

abbrev Data (K L Addr : Type) [Field K] (s m : ℕ) := L → Fin s → Addr → Coeff K m

/-- Decode/encode the ordinary extension rows only at aligned addresses. The
movement between these two operations uses base-field symbols. -/
def predict [Fintype L] [DecidableEq L] [Fintype B] [Fintype H]
    (r : B → Rectangle L) (I J : H → L) (M : Matrix H H K) (e : Environment K m)
    (g : StageRoute.Layout r (Fin m) Addr) (x : Data K L Addr (width m) m) :
    Data K L Addr (width m) m :=
  let stream (w : L) (a : Addr) (t : PackedPencil.Index m) := components K m (x w t.1 a) t.2
  let y := (StageScript.eval g.perm (PackedPencil.program r I J M e))^[order m] stream
  fun w i a => (components K m).symm (fun d => y w a (i,d))

theorem predict_on_fibre [Fintype L] [DecidableEq L] [Fintype B] [Fintype H]
    (r : B → Rectangle L) (I J : H → L) (M : Matrix H H K) (e : Environment K m)
    (g : StageRoute.Layout r (Fin m) Addr)
    (hM : (rectangleMatrix (K := K) r).submatrix id J * M *
        (rectangleMatrix r).submatrix I id = rectangleMatrix r)
    (key : Address (Fin m) C → Addr)
    (hswap : ∀ j w a, (g.S j w).symm (g.T j w (key a)) = key (swap j a))
    (x : Data K L Addr (width m) m) (w : L) :
    (fun i a => predict r I J M e g x w i (key a)) =
      (SwapRepair.stage e)^[order m] (fun i a => x w i (key a)) := by
  let stream (w : L) (a : Addr) (t : PackedPencil.Index m) := components K m (x w t.1 a) t.2
  have h := PackedPencil.iterate_on_fibre r I J M e g hM key hswap stream w (order m)
  have hs : pack (fun i d a => stream w (key a) (i,d)) = fun i a => x w i (key a) := by
    funext i a
    dsimp only [pack, stream]
    rw [LinearEquiv.symm_apply_apply]
  rw [hs] at h
  exact h

/-- A fixed lookup on the low-codimension spectral rows. The pattern stream has
one bit per main pair and can be shared across the two output columns. -/
def checksTable (T : Table K m) (tag : Addr → Pattern m)
    (forward backward : (Addr → Coeff K m) → Addr → Coeff K m)
    (v₁ v₂ : Data K L Addr (checks m) m) :
    Data K L Addr (checks m) m × Data K L Addr (checks m) m :=
  let output w a := T (tag a) (fun i => forward (v₁ w i) a, fun i => forward (v₂ w i) a)
  (fun w i => backward (fun a => (output w a).1 i),
   fun w i => backward (fun a => (output w a).2 i))

/-- Four predictors, four check-row conversions per check and label, and
ordinary aligned row tables. The same first prediction supplies the checks and
the cubic Hermite correction. -/
def schedule (e : Environment K m) (T : Table K m) (tag : Addr → Pattern m)
    (forward backward : (Addr → Coeff K m) → Addr → Coeff K m)
    (P : Data K L Addr (width m) m → Data K L Addr (width m) m)
    (x : Data K L Addr (width m) m) : Data K L Addr (width m) m :=
  let H := repairCheck e.nodes (checks m)
  let px := P x
  let t := checksTable T tag forward backward (fun w => repairMixRows H (px w))
    (fun w => repairMixRows H (x w))
  let z := P (fun w => repairMixRows Hᵀ (t.1 w))
  let fz w := repairMixRows Hᵀ (t.2 w)
  let cube := P (P px)
  fun w i => px w i - e.invRadix • (cube w i - px w i) - z w i + fz w i

theorem inv_two (e : Environment K m) : (2 : Coeff K m) * e.invRadix = 1 := by
  simpa only [mul_comm, Nat.cast_ofNat] using e.invRadix_mul

private theorem mix_restrict {n s : ℕ} (H : Matrix (Fin n) (Fin s) (Coeff K m))
    (x : Fin s → Addr → Coeff K m) (key : Address (Fin m) C → Addr) :
    (fun i a => repairMixRows H x i (key a)) =
      repairMixRows H (fun i a => x i (key a)) := by
  ext
  simp [repairMixRows, Finset.sum_apply]

theorem schedule_on_fibre [LinearOrder C] (e : Environment K m) (T : Table K m)
    (tag : Addr → Pattern m) (forward backward : (Addr → Coeff K m) → Addr → Coeff K m)
    (P : Data K L Addr (width m) m → Data K L Addr (width m) m)
    (key : Address (Fin m) C → Addr) (w : L)
    (hP : ∀ x, (fun i a => P x w i (key a)) =
      (SwapRepair.stage e)^[order m] (fun i a => x w i (key a)))
    (hf : ∀ x, forward x ∘ key = spectrum (List.finRange m) e.invRadix (inv_two e) (x ∘ key))
    (hb : ∀ x, backward x ∘ key = (spectrum (List.finRange m) e.invRadix (inv_two e)).symm (x ∘ key))
    (ht : ∀ a, tag (key a) = pattern a)
    (x : Data K L Addr (width m) m) :
    (fun i a => schedule e T tag forward backward P x w i (key a)) =
      SwapRepair.run e T (fun i a => x w i (key a)) := by
  let S := spectrum (List.finRange m) e.invRadix (inv_two e) (C := C)
  have table_restrict (u v : Data K L Addr (checks m) m) :
      (fun i a => (checksTable T tag forward backward u v).1 w i (key a),
       fun i a => (checksTable T tag forward backward u v).2 w i (key a)) =
        ordinaryRepairTable S (T ∘ pattern) (fun i a => u w i (key a)) (fun i a => v w i (key a)) := by
    apply Prod.ext <;> funext i
    all_goals
      change backward _ ∘ key = S.symm _
      rw [hb]
      apply congrArg S.symm
      funext a
      dsimp only [Function.comp_apply]
      simp_rw [ht, show ∀ y, forward y (key a) = S (y ∘ key) a from fun y => congrFun (hf y) a]
      rfl
  let H := repairCheck e.nodes (checks m)
  let px := P x
  let t := checksTable T tag forward backward (fun w => repairMixRows H (px w)) (fun w => repairMixRows H (x w))
  let P' := (SwapRepair.stage (C := C) e)^[order m]
  let t' := ordinaryRepairTable S (T ∘ pattern) (repairMixRows H (P' (fun i a => x w i (key a))))
    (repairMixRows H (fun i a => x w i (key a)))
  have ht' : ((fun i a => t.1 w i (key a)), fun i a => t.2 w i (key a)) = t' := by
    dsimp only [t, t']
    rw [table_restrict, mix_restrict, mix_restrict, hP]
  have hcube : (fun i a => P (P px) w i (key a)) = P' (P' (P' (fun i a => x w i (key a)))) := by
    rw [hP, hP, hP]
  have hz : (fun i a => P (fun w => repairMixRows Hᵀ (t.1 w)) w i (key a)) =
      P' (repairMixRows Hᵀ t'.1) := by
    rw [hP, mix_restrict, show (fun i a => t.1 w i (key a)) = t'.1 from congrArg Prod.fst ht']
  have hfz : (fun i a => repairMixRows Hᵀ (t.2 w) i (key a)) = repairMixRows Hᵀ t'.2 := by
    rw [mix_restrict, show (fun i a => t.2 w i (key a)) = t'.2 from congrArg Prod.snd ht']
  funext i a
  change px w i (key a) - e.invRadix * (P (P px) w i (key a) - px w i (key a)) -
    P (fun w => repairMixRows Hᵀ (t.1 w)) w i (key a) + repairMixRows Hᵀ (t.2 w) i (key a) =
    _ - e.invRadix * ((P'^[2] _) i a - _) - _ + _
  rw [congrFun (congrFun hz i) a, congrFun (congrFun hfz i) a, congrFun (congrFun hcube i) a,
    show px w i (key a) = P' (fun i a => x w i (key a)) i a from congrFun (congrFun (hP x) i) a]
  rfl

end Interchange.RepairSchedule

end

end NearSquareRoot
end Computability
end OAI
