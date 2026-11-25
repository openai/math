import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelectedSweepPrice
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweepBankOpen
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelectedLeafStep

/-! # Open execution on precisely the requests emitted by each native sweep -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.Physical.Selected

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  Space InterchangeROMAddress InterchangeAddress InterchangeROM InterchangeSpace
  Interchange.Template InterchangeSpectralFibre

open private sweepPrice_le from OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelectedSweepPrice

private theorem peak_map {T : Type} (p : T → ℕ) (qs : List T) :
    (qs.map p).foldr max 0 = childPeak p qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp only [List.map_cons,List.foldr_cons,childPeak,ih]

variable {j threshold w f : ℕ} {x : Data} [Fact (x.modulusIndex+1).Prime] [NeZero x.b]
    {P G S : Tape} {D : Type}

local notation "H" => send (InterchangeROMAddress.header f P G S)
local notation "L" => SweepBank.layout P G S x.a x.m x.b f

omit [NeZero x.b] in
theorem sweep_step (h : Data.Valid j threshold x) (ok : ∀ k ∈ P++G++S, 2 ≤ k ∧ k ≤ x.b)
    (pay : Series D) (hw : pay.count ≤ w) (inv : Bool) (u v : x.Short P G S f D) :
    let qs := SweepBank.emitted w pay (half x) inv u v
    let M := InterchangeROMStageVolume.mass H (L).count w
    let out := sweep (lift (directions inv x.half))
    InterchangeROMSequence.Step (Request.job x.b) (sweepLeaf x inv) H
      (Task.forest id (shortBank x P G S f pay u ++ shortBank x P G S f pay v))
      (packet H (shortBank x P G S f pay (out u) ++ shortBank x P G S f pay (out v))) qs
      (sweepFactor x*M) (sweepFactor x*M) (sweepFactor x*M) := by
  intro qs M out parent env price data depth solves r base hr
  let C := (L).count*(w+1)+1
  let child (q : Request x.b) : Allowance := ⟨price q,data q,depth q⟩
  have hm : 0 < x.m := lt_of_lt_of_le (by decide : 0 < 2) h.1.2.2.2.2.2.1
  have cm : C ≤ M := by dsimp [C,M,InterchangeROMStageVolume.mass]; omega
  have kt := Nat.mul_le_mul (sweepPrice_le x inv).1 cm
  have ks := Nat.mul_le_mul (sweepPrice_le x inv).2 cm
  have run := SweepBank.command_priced_on hm h.1.2.2.1.two_le ok pay hw parent env child
    (half x) inv u v solves r base hr
  change BoundedFits _ _ _ _
    ((sweepPrice x inv).1*C+(qs.map price).sum) (base+((sweepPrice x inv).2*C+(qs.map data).foldr max 0))
    ((sweepPrice x inv).2*C+(qs.map depth).foldr max 0) at run
  rw [peak_map,peak_map] at run
  exact run.mono (Nat.add_le_add_right kt _) (by omega) (Nat.add_le_add_right ks _)

/-- Both directions satisfy the selected phase bound with their ordered, typed
dockets and arbitrary individual child prices. -/
theorem sweep_leaves (h : Data.Valid j threshold x) (ok : ∀ k ∈ P++G++S, 2 ≤ k ∧ k ≤ x.b)
    (pay : Series D) (hw : pay.count ≤ w) (inv : Bool) (u v : x.Short P G S f D) :
    let M := InterchangeROMStageVolume.mass H (L).count w
    let out := sweep (lift (directions inv x.half))
    LeafStep h P G S f pay w (sweepFactor x*M) (if inv then .backward else .forward)
      (shortBank x P G S f pay u ++ shortBank x P G S f pay v)
      (shortBank x P G S f pay (out u) ++ shortBank x P G S f pay (out v)) := by
  intro M out
  refine ⟨SweepBank.emitted w pay (half x) inv u v,?_,?_,?_⟩
  · rw [SweepBank.emitted_length]
    cases inv <;> simp [phaseCalls,price,Nat.mul_assoc]
  · intro q hq
    have z := SweepBank.emitted_typed w pay (half x) inv u v q hq
    exact ⟨z.1.1,z.1.2,z.2⟩
  · cases inv <;> exact sweep_step h ok pay hw _ u v

end InterchangeROMRepair.Physical.Selected

end

end NearSquareRoot
end Computability
end OAI
