import OAI.Computability.BorderVNP.PackedBankPublicReplay

/-! # Descriptor and expanded capacity of the same genuine site program -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening
open scoped Classical

/-- Public words and separately charged expanded work fit the corresponding record fields
on every tested region, in either mode. -/
theorem bankRecords_le {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (pr : Site.Programs N) (data : Epoch.Round.RecordData N) (ex : Bool)
    (hold : ∀ v, (pr v).program.publicNodes ≤ data.prior v ∧ (pr v).program.expandedLoad ≤ data.payload v)
    (test : N.Site → Prop) :
    localRecords N ex pr.bankFields.prior pr.bankFields.payload test ≤ localRecords N ex data.prior data.payload test := by
  unfold localRecords
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply Finset.sum_le_sum
  intro v _
  by_cases h : test v
  · have hv := hold v
    cases ex <;> simp only [h,ite_true,boxCost,recordCost,Bool.false_eq_true,ite_false,Nat.add_zero,
      Site.Programs.bankFields,Subdivision.publicProgramData] <;> omega
  · simp [h]

end Packing.Inherited

namespace PackedHistoryCircuit.Normalized.Program

open Cover Crossing Shortening Shortening.Adaptive Packing Packing.Inherited InheritedBank Epoch.Round
open scoped Classical
attribute [local instance] portFintype

variable {D m k rounds : ℕ} [NeZero D] {I P K : Type} [Fintype P] [Fintype I] [Field K] {bits : P → ℕ}
    {A : ℕ → Type*} {B : Fin rounds → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {e : PaidIdentity K D m} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    (F : Program (B := B) e view) (store : F.SaveNames) (rows : F.SiteRows) (number : e.Entry → ℕ)

/-- The same flattened private program satisfies the descriptor and expanded budgets
on its genuine final route, from its public fields and its separate expanded load. -/
theorem flatPrivatePrograms_bankRecords {dst : ℕ} {L W X : ℝ} {H : ℕ} (C : Fin rounds → ℕ)
    (cert : ∀ i c, (F.stage i c).RecordFactor e (C i)) (ex : Bool) (T : ℕ) (hT : 0 < T)
    (flat : Fin (k^rounds) → A 0) (data : ∀ i, RecordData (view 0 (flat i)).pack.layout)
    (pr : ∀ i, Site.Programs (view 0 (flat i)).pack.layout)
    (base : ∀ i v, (pr i v).program.publicNodes ≤ (data i).prior v ∧ (pr i v).program.expandedLoad ≤ (data i).payload v)
    (old : ∀ i, RecordsWithin (view 0 (flat i)) (data i) ex T) (q : F.Hist flat)
    (out : SiteOutput (F.terminal flat q) dst L W X H) (tile) :
    let N := (flattenPack rounds (F.terminal flat q).pack).layout
    let current := F.flatPrivatePrograms store rows number flat pr q
    1+localRecords N ex current.bankFields.prior current.bankFields.payload
      (fun v => reduceMove dst (out.routes.flatten.origin v) = tile) ≤ (1+H)*(1+∑ i, loadMultiplier e*C i*k)^rounds*T := by
  let current := F.flatPrivatePrograms store rows number flat pr q
  let p := F.terminal flat q
  let N := (flattenPack rounds p.pack).layout
  let fields := F.replayBankRecords store rounds le_rfl flat data q
  let test (v : N.Site) := reduceMove dst (out.routes.flatten.origin v) = tile
  have fit : ∀ v, (current v).program.publicNodes ≤ fields.prior v :=
    F.replayPrivatePrograms_public_le store rows number rounds le_rfl flat data pr (fun i v => (base i v).1) q
  have expanded : ∀ v, (current v).program.expandedLoad ≤ fields.payload v :=
    F.replayPrivatePrograms_expanded_le store rows number rounds le_rfl flat data pr (fun i v => (base i v).2) q
  let flatFields : RecordData N := ⟨fields.prior,fields.payload⟩
  have pub := bankRecords_le N current flatFields ex (fun v => ⟨fit v,expanded v⟩) test
  have history := F.replayBankRecords_bound store C cert ex T hT rounds le_rfl flat data old q
  have rounded := flat_output_record_bound p out fields ex (Nat.mul_pos (pow_pos (Nat.add_pos_left (by decide) _) _) hT) history tile
  exact (Nat.add_le_add_left pub 1).trans (rounded.trans_eq (by ring))


end PackedHistoryCircuit.Normalized.Program

end BorderVNP
end Computability
end OAI
