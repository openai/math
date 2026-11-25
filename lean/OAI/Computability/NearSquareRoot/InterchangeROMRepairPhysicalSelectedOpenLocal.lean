import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelectedOpen

/-! # Discharging ordinary phases of the open recursive selected command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.Physical.Selected

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom
  IntegerMultiplication.Strip.Dims Space InterchangeSpace InterchangeROM InterchangeROMAddress
  Interchange.Template

variable {j threshold f : ℕ} {x : Data} {P G S : Tape} {D Q : Type}
variable [Fact (x.modulusIndex+1).Prime] [NeZero x.b]

set_option maxHeartbeats 800000 in
private theorem empty_local_step (h : Data.Valid j threshold x) (pay : Series D) (width : ℕ)
    (hw : pay.count ≤ width) (job : Job Q) {k u v} (tr : transfer h P G S f pay k u v)
    (localPhase : ¬ LocalTable.Lift.Routed k) :
    let H := send (header f P G S)
    let M := InterchangeROMStageVolume.mass H (SweepBank.layout P G S x.a x.m x.b f).count width
    let cost := ordinaryFactor x*M
    InterchangeROMSequence.Step job (commands x k) H (Task.forest id u) (packet H v) [] cost cost cost := by
  intro H M cost parent env time data depth _ deck base hd
  have hl : 0 < x.labels := h.1.2.2.2.2.2.2.1
  have hrow : 0 < Raw.rowCount x.m := by
    unfold Raw.rowCount Sizes.rows Sizes.basisCount Sizes.pencilOrder
    positivity
  have actual := LocalTable.Lift.local_transition x.repair (SweepBank.layout P G S x.a x.m x.b f)
    (fun _ => pay) Prod.mk H width (fun _ => hw) (Nat.mul_pos hl hrow) (commands x) tr localPhase
    (parent::env) deck base hd
  change BoundedFits (parent::env) (LocalTable.Lift.choose (matrixLeaf x) (commands x) k)
    (pile 0 (packet H u) deck) (pile 0 (packet H v) deck) cost (base+cost) cost at actual
  have eq : LocalTable.Lift.choose (matrixLeaf x) (commands x) k = commands x k := by cases k <;> rfl
  rw [eq] at actual
  simp only [List.map_nil,List.sum_nil,Nat.add_zero,childPeak,List.foldr_nil]
  exact actual

/-- Local expansion of any open physical stage, with the same finite list. -/
theorem extend_open {Q : Type} {job : Job Q} {c : Cmd} {h u v : Tree} {qs : List Q} {t s d b : ℕ}
    (run : InterchangeROMSequence.Step job c h u v qs t s d) (ht : t ≤ b) (hs : s ≤ b) (hd : d ≤ b) :
    InterchangeROMSequence.Step job c h u v qs b b b := by
  intro parent env price data depth solve deck base cap
  exact (run parent env price data depth solve deck base cap).mono (Nat.add_le_add_right ht _)
    (Nat.add_le_add_right (Nat.add_le_add_left hs base) _) (Nat.add_le_add_right hd _)

/-- Five arithmetic phases compile without calling the parent. Each of the
remaining four phases supplies its real list of parent invocations. -/
theorem program_open_of_routed (h : Data.Valid j threshold x) (pay : Series D) (width : ℕ)
    (hw : pay.count ≤ width) (job : Job Q) (valid : Q → Prop) (L : ℕ)
    (routed : ∀ k u v, LocalTable.Lift.Routed k → transfer h P G S f pay k u v →
      let H := send (header f P G S)
      let z := L*InterchangeROMStageVolume.mass H (SweepBank.layout P G S x.a x.m x.b f).count width
      ∃ qs : List Q, qs.length ≤ phaseCalls h k ∧ (∀ q∈qs, valid q) ∧
        InterchangeROMSequence.Step job (commands x k) H (Task.forest id u) (packet H v) qs z z z)
    (u : x.Wide P G S f D) :
    let H := send (header f P G S)
    let M := InterchangeROMStageVolume.mass H (SweepBank.layout P G S x.a x.m x.b f).count width
    ∃ qs : List Q, qs.length ≤ x.calls ∧ (∀ q ∈ qs, valid q) ∧ ∀ parent,
      InterchangeROMRecursion.At parent (program x) job qs [] (packet H (wideBank x P G S f pay u))
        (packet H (wideBank x P G S f pay (swapPayload u))) (compiledRate x (max L (ordinaryFactor x))*M) 0 0 := by
  apply program_open_of_phases h pay width hw job valid (max L (ordinaryFactor x)) _ u
  intro k v z tr
  let M := InterchangeROMStageVolume.mass (send (header f P G S)) (SweepBank.layout P G S x.a x.m x.b f).count width
  by_cases hr : LocalTable.Lift.Routed k
  · obtain ⟨qs,hlen,hval,run⟩ := routed k v z hr tr
    have le := Nat.mul_le_mul_right M (le_max_left L (ordinaryFactor x))
    exact ⟨qs,hlen,hval,extend_open run le le le⟩
  · have le := Nat.mul_le_mul_right M (le_max_right L (ordinaryFactor x))
    exact ⟨[],Nat.zero_le _,by simp,extend_open (empty_local_step h pay width hw job tr hr) le le le⟩

end InterchangeROMRepair.Physical.Selected

end

end NearSquareRoot
end Computability
end OAI
