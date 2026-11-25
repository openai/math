import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelectedOpenLocal
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelectedOpenCases
import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectPacked

/-! # The compiled native interchange, with its physical recursive requests -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Selected

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims Space InterchangeSpace InterchangeROM InterchangeROMAddress
  Interchange.Template InterchangeAddress

/-- The command is the single effective template compiler `Selected.program`.
Its local cost has one absolute header exponent and a computable template factor.
Each actual recursive invocation retains its original payload and width. -/
theorem program_native : ∃ e : ℕ, 1 ≤ e ∧ ∃ K : Data → ℕ, Computable K ∧
    ∀ {j threshold f width : ℕ} {x : Data} [NeZero x.b] [Fact (x.modulusIndex+1).Prime]
      (_ : Data.Valid j threshold x) {P G S : Tape} (_ : ∀ k∈P++G++S, 2≤k ∧ k≤x.b)
      {D : Type} (pay : Series D) (_ : pay.count ≤ width) (u : x.Wide P G S f D),
      let hdr := header f P G S
      let H := send hdr
      let N := (x.stageRows P G S f).count
      let M := InterchangeROMStageVolume.mass H N (width+(size hdr+1)^e)
      ∃ qs : List (Request x.b), qs.length ≤ x.calls ∧
        (∀ y ∈ qs, OpcodeProgram.Valid f N width P G S (x.recordGood pay) y) ∧ ∀ parent,
        InterchangeROMRecursion.At parent (program x) (Request.job x.b) qs []
          (packet H (wideBank x P G S f pay u)) (packet H (wideBank x P G S f pay (swapPayload u)))
          (K x*M) 0 0 := by
  obtain ⟨e,he,L,hL,route⟩ := routed_open
  refine ⟨e,he,fun x => compiledRate x (max (L x) (ordinaryFactor x)),
    computable_compiledRate (Primrec.nat_max.to_comp.comp hL computable_ordinaryFactor),?_⟩
  intro j threshold f width x nz prime h P G S ok D pay hw u
  let big := width+(size (header f P G S)+1)^e
  have hbig : pay.count ≤ big := hw.trans (Nat.le_add_right width _)
  exact program_open_of_routed h pay big hbig (Request.job x.b)
    (OpcodeProgram.Valid f (x.stageRows P G S f).count width P G S (x.recordGood pay)) (L x)
    (route h ok pay hw) u

/-- At the center-machine ABI, every element of the open ledger is a packed,
admissible smaller interchange with the same ground alphabet and record width. -/
theorem program_packed : ∃ e : ℕ, 1 ≤ e ∧ ∃ K : Data → ℕ, Computable K ∧
    ∀ {j threshold f width : ℕ} {x : Data} [NeZero x.b] [Fact (x.modulusIndex+1).Prime]
      (_ : Data.Valid j threshold x) {P G S : Tape} (_ : ∀ k∈P++G++S, 2≤k ∧ k≤x.b)
      (_ : 0 < f) (u : x.Wide P G S f (Fin width)),
      let pay := Series.natural width
      let hdr := header f P G S
      let H := send hdr
      let N := (x.stageRows P G S f).count
      let M := InterchangeROMStageVolume.mass H N (width+(size hdr+1)^e)
      ∃ qs : List (Request x.b), qs.length ≤ x.calls ∧
        (∀ y ∈ qs, y.Packed (fun a : x.Ground => InterchangeROMTable.numeral a.val) ∧
          y.width=f ∧ y.recordWidth=width ∧ y.rows.count=N) ∧ ∀ parent,
        InterchangeROMRecursion.At parent (program x) (Request.job x.b) qs []
          (packet H (wideBank x P G S f pay u)) (packet H (wideBank x P G S f pay (swapPayload u)))
          (K x*M) 0 0 := by
  obtain ⟨e,he,K,hK,run⟩ := program_native
  refine ⟨e,he,K,hK,?_⟩
  intro j threshold f width x nz prime h P G S ok hf u
  obtain ⟨qs,count,typed,actual⟩ := run h ok (Series.natural width) (Series.count_natural width).le u
  exact ⟨qs,count,fun y hy => Data.packed_of_opcode_valid h hf ok (typed y hy),actual⟩

end InterchangeROMRepair.Physical.Selected

end NearSquareRoot
end Computability
end OAI
