import OAI.Computability.BorderVNP.PackedBankProgramCapacity

/-! # Full stored program size on the original normalized history

The full prior charges each one-copy table and its resolved sweeps. Its tile
budget starts from the stored bottom programs and is independent of the smaller
budget for public row words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening
open scoped Classical

/-- Full stored one-copy program and the separately charged expanded work at
each physical site. -/
def Site.Programs.fullFields {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
    (pr : Site.Programs N) : Epoch.Round.RecordData N :=
  ⟨fun v => (pr v).program.staticNodes,fun v => (pr v).program.expandedLoad⟩

/-- Stored one-copy table and separately charged expanded work fit the corresponding record fields
on every tested region, in either mode. -/
theorem fullRecords_le {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (pr : Site.Programs N) (data : Epoch.Round.RecordData N) (ex : Bool)
    (hold : ∀ v, (pr v).program.staticNodes ≤ data.prior v ∧ (pr v).program.expandedLoad ≤ data.payload v)
    (test : N.Site → Prop) :
    localRecords N ex pr.fullFields.prior pr.fullFields.payload test ≤ localRecords N ex data.prior data.payload test := by
  unfold localRecords
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply Finset.sum_le_sum
  intro v _
  by_cases h : test v
  · have hv := hold v
    cases ex <;> simp only [h,ite_true,boxCost,recordCost,Bool.false_eq_true,ite_false,Nat.add_zero,
      Site.Programs.fullFields] <;> omega
  · simp [h]

end Packing.Inherited

namespace PackedHistoryCircuit.Normalized.Stage

open Cover Crossing Shortening Shortening.Adaptive Packing Packing.Inherited Epoch.Round
open scoped Classical

variable {D m k d d' : ℕ} [NeZero D] {I P K Bin : Type} [Fintype P] [Fintype I] [Fintype Bin] [Field K]
    {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d} (s : Stage m Bin d' child) (e : PaidIdentity K D m)
    (q : s.Index e) (old : ∀ j, Site.Programs (child j).pack.layout) (data : ∀ j, RecordData (child j).pack.layout)
    {ns ne np : ℕ} (sites : (s.result e q).pack.layout.Site ↪ Fin ns) (edges : (s.result e q).pack.layout.Edge ↪ Fin ne)
    (ports : Fin k × P ↪ Fin np) (seeds : ((I → Deck (d'+1)) × Bin) → ℕ) (number : e.Entry → ℕ)

/-- All stored factor rows, emitted guard records and one-copy sweep entries of
an attained stage fit its full prior. -/
theorem privatePrograms_static_le (hold : ∀ j v, (old j v).program.staticNodes ≤ (data j).prior v)
    (v : (s.result e q).pack.layout.Site) :
    (s.privatePrograms e q old sites edges ports seeds number v).program.staticNodes ≤ (s.bankRecordData e q data).prior v := by
  let previous := fun u : s.input.layout.Site => (old u.1 u.2).program
  let oldID := CutCircuit.denseRows (raw child).layout s.slot
  let cuts := fun u => Layer.orderedCuts s.input oldID ports u e s.label s.perm seeds s.orient (0,false) q edges
  have h := roundSites_charged e s.input s.label s.perm s.orient (0,false) q seeds number sites edges ports previous cuts
    (fun u => (data u.1).prior u.2) (fun u => (previous u).expandedLoad)
    (fun u => (old u.1 u.2).size.trans (s.input_incoming u.1 u.2).symm) (fun u => ⟨hold u.1 u.2,le_rfl⟩)
    (cuts_length_of_perm e s.input s.label s.perm s.orient (0,false) q seeds edges ports cuts oldID
      (fun u => Layer.ordered_perm s.input oldID ports u e s.label s.perm seeds s.orient (0,false) q edges)) v
  rcases v with oldV | fresh <;> exact h.1

end PackedHistoryCircuit.Normalized.Stage

namespace PackedHistoryCircuit.Normalized.Program

open private nested_bankRelation from OAI.Computability.BorderVNP.PackedBankPublicReplay

open Cover Crossing Shortening Shortening.Adaptive Packing Packing.Inherited InheritedBank Epoch.Round
open scoped Classical
attribute [local instance] portFintype

variable {D m k rounds : ℕ} [NeZero D] {I P K : Type} [Fintype P] [Fintype I] [Field K] {bits : P → ℕ}
    {A : ℕ → Type*} {B : Fin rounds → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {e : PaidIdentity K D m} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
    (F : Program (B := B) e view) (store : F.SaveNames) (rows : F.SiteRows) (number : e.Entry → ℕ)

/-- Full stored programs at retained and fresh sites are dominated pointwise by the
full one-copy prior on the original selected normalized histogram. -/
theorem replayPrivatePrograms_static_le (n : ℕ) (hn : n ≤ rounds) (flat : Fin (k^n) → A 0)
    (data : ∀ i, RecordData (view 0 (flat i)).pack.layout) (pr : ∀ i, Site.Programs (view 0 (flat i)).pack.layout)
    (base : ∀ i v, (pr i v).program.staticNodes ≤ (data i).prior v) (q : F.FlatHist n hn flat) :
    let start := nestedPrivatePrograms (fun x => (view 0 x).pack) n flat pr
    let current := F.replayPrivatePrograms store rows number n hn (leavesEquiv k _ n flat) start q
    let fields := F.replayBankRecords store n hn flat data q
    ∀ v, (current v).program.staticNodes ≤ fields.prior v := by
  let R := fun (_ : ℕ) (s : Site) (p _ : ℕ) => s.staticNodes ≤ p
  exact F.replayPrivatePrograms_bankRelation store rows number R
    (fun i c q old fields h => (F.stage i c).privatePrograms_static_le e q old fields (rows.sites i c q)
      (store.number i c q) (rows.ports (i.val+1)) (rows.seeds i) number h) n hn flat data _
    (nested_bankRelation (view := view) (R 0) n flat data pr base) q

/-- The same flattened private program satisfies the descriptor and expanded budgets
on its genuine final route, from its full stored program and its separate expanded load. -/
theorem flatPrivatePrograms_fullRecords {dst : ℕ} {L W X : ℝ} {H : ℕ} (C : Fin rounds → ℕ)
    (cert : ∀ i c, (F.stage i c).RecordFactor e (C i)) (ex : Bool) (T : ℕ) (hT : 0 < T)
    (flat : Fin (k^rounds) → A 0) (data : ∀ i, RecordData (view 0 (flat i)).pack.layout)
    (pr : ∀ i, Site.Programs (view 0 (flat i)).pack.layout)
    (base : ∀ i v, (pr i v).program.staticNodes ≤ (data i).prior v ∧ (pr i v).program.expandedLoad ≤ (data i).payload v)
    (old : ∀ i, RecordsWithin (view 0 (flat i)) (data i) ex T) (q : F.Hist flat)
    (out : SiteOutput (F.terminal flat q) dst L W X H) (tile) :
    let N := (flattenPack rounds (F.terminal flat q).pack).layout
    let current := F.flatPrivatePrograms store rows number flat pr q
    1+localRecords N ex current.fullFields.prior current.fullFields.payload
      (fun v => reduceMove dst (out.routes.flatten.origin v) = tile) ≤ (1+H)*(1+∑ i, loadMultiplier e*C i*k)^rounds*T := by
  let current := F.flatPrivatePrograms store rows number flat pr q
  let p := F.terminal flat q
  let N := (flattenPack rounds p.pack).layout
  let fields := F.replayBankRecords store rounds le_rfl flat data q
  let test (v : N.Site) := reduceMove dst (out.routes.flatten.origin v) = tile
  have fit : ∀ v, (current v).program.staticNodes ≤ fields.prior v :=
    F.replayPrivatePrograms_static_le store rows number rounds le_rfl flat data pr (fun i v => (base i v).1) q
  have expanded : ∀ v, (current v).program.expandedLoad ≤ fields.payload v :=
    F.replayPrivatePrograms_expanded_le store rows number rounds le_rfl flat data pr (fun i v => (base i v).2) q
  let flatFields : RecordData N := ⟨fields.prior,fields.payload⟩
  have pub := fullRecords_le N current flatFields ex (fun v => ⟨fit v,expanded v⟩) test
  have history := F.replayBankRecords_bound store C cert ex T hT rounds le_rfl flat data old q
  have rounded := flat_output_record_bound p out fields ex (Nat.mul_pos (pow_pos (Nat.add_pos_left (by decide) _) _) hT) history tile
  exact (Nat.add_le_add_left pub 1).trans (rounded.trans_eq (by ring))


end PackedHistoryCircuit.Normalized.Program

end BorderVNP
end Computability
end OAI
