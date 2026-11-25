import OAI.Computability.BorderVNP.DiagonalPayloadBound
import OAI.Computability.BorderVNP.DiagonalSpecializedDenseStep
import OAI.Computability.BorderVNP.ShortenEpochRoundDenseRecords

/-!
# Scalar multiplicities in a field-specialized dense crossing

The tag at a retained site is the child table at its reconstructed local
wires. Each new paid box contributes one scalar factor per selected copy,
exactly the population charged to that site's sewn payload. This bound
applies to every assignment of the local inputs of the actual tagged table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Shortening Shortening.SeedIntervals Packing PackedHistoryCircuit.Normalized
open scoped BigOperators Classical

variable {Param Gadget : Type*}

private theorem guarded_counter (ok : Prop) [Decidable ok] (g : Gadget) :
    (counters (if ok then (1 : Entry Param Gadget) else 0)).2 g ≤ 0 := by
  split <;> rfl

/-- Every copy contributes at most one occurrence of a fixed scalar
position, including when different addresses use the same position. -/
theorem gadget_product_count_le {n : ℕ} (position : Fin n → Gadget) (g : Gadget) :
    (counters (∏ i, gadget (Param := Param) (position i))).2 g ≤ n := by
  rw [counters_prod (fun i => gadget (Param := Param) (position i)) (fun _ => WithZero.coe_ne_zero),
    counters_passed,Finsupp.finsetSum_apply]
  calc
    _ ≤ ∑ _ : Fin n, (1 : ℕ) := Finset.sum_le_sum fun i _ => by
      simp only [gadget,counters_passed,Finsupp.single_apply]
      split <;> omega
    _ = _ := by simp

/-- The two Boolean guard types have zero scalar count. Each paid tensor
box has count bounded by the number of occurrences of its selected term. -/
theorem profileTags_payloadBound {D m : ℕ} {E : Type*} [Field E] (e : PaidIdentity E D m)
    (position : e.Entry → Gadget) (j : ℕ) (p : Fin e.count → ℕ) (first : Fin D × Bool) :
    PayloadBound (profileTags (Param := Param) e position j p first) (bankUses e j p) := by
  intro v z x g
  rcases v with ⟨⟩ | u | ⟨a,v⟩
  · exact guarded_counter _ g
  · exact guarded_counter _ g
  · exact gadget_product_count_le (n := p a) _ g

namespace DenseReplay

variable {D m k d next exp : ℕ} [NeZero D] {I P B : Type} [Fintype I] [Fintype B]
    {bits : P → ℕ} {Team Param Gadget K E : Type} [Fintype Team] [Fintype Param] [Field K] [Field E]
    {child : Fin k → PlacedPack D P bits K I d}
    (s : Stage m B next child) (input : ∀ i, Tracked Team Param Gadget exp (child i).pack.layout)
    (e : PaidIdentity K D m) (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget)

omit [Field K] in
/-- The unaltered old-site counter bound after parallel joining and
sorting all sparse cable IDs into the interval allocator's order. -/
theorem ordered_payloadBound (payload : ∀ i, (child i).pack.layout.Site → ℕ)
    (old : ∀ i, PayloadBound (input i).tags (payload i)) :
    PayloadBound (ordered s input).tags (fun v => payload v.1 v.2) := by
  have mergedBound : PayloadBound (merged input).tags (fun v => payload v.1 v.2) :=
    fun v _ _ g => old v.1 v.2 _ _ g
  exact mergedBound.stored (Storage.dense (raw child).layout s.slot)

set_option maxHeartbeats 600000 in
/-- For every histogram of the reference-field physical stage, each scalar
count in the actual specialized tagged output is bounded by its particular
retained payload or paid term-copy charge. Different entries may use the same scalar position. -/
theorem stageOutput_payloadBound (q : s.Index e) (payload : ∀ i, (child i).pack.layout.Site → ℕ)
    (old : ∀ i, PayloadBound (input i).tags (payload i)) :
    PayloadBound (stageOutput s input e y hy pos q).tags (s.resultPayload e q payload) := by
  have h := ordered_payloadBound s input payload old
  intro v z x g
  rcases v with v | ⟨a,v⟩
  · dsimp only [stageOutput,roundTags,seedTags,Network.sewTables,Network.cutTables,roundPieces,
      Network.bandTables,Stage.resultPayload,sewnPayload,Sum.elim_inl]
    exact h v _ _ g
  · dsimp only [stageOutput,roundTags,seedTags,Network.sewTables,seedInner,AddressPartition.parallelTables,
      Bundle.exposeTables,Stage.resultPayload,sewnPayload,Sum.elim_inr]
    apply (profileTags_payloadBound (e.specialize y hy) pos (s.matched a) (q a).val (0,false) v _ _ g).trans_eq
    rcases v with v | v | ⟨term,v⟩ <;> rfl

end DenseReplay
end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
