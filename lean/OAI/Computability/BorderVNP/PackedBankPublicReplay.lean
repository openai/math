import OAI.Computability.BorderVNP.PackedBankCoupledReplay
import OAI.Computability.BorderVNP.PackedBankPublicSubdivision
import OAI.Computability.BorderVNP.PackedHistoryFlatPrivateSites

/-! # Public word bounds on the original normalized private programs

The public count at a site includes its record fields, guards and one name per
opaque box. Its private tables may be arbitrarily larger. The true program
and the numerical bank records follow the same histogram and the same two
cable orderings. The public record cap bounds the words printed in each tile.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening CellSparse
open scoped Classical

/-- Exact public count and expanded work of a family of physical site programs. -/
abbrev Site.Programs.bankFields {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
    (pr : Site.Programs N) : Epoch.Round.RecordData N := Subdivision.publicProgramData pr

/-- In descriptor mode only the public prior of each site enters the box charge. -/
theorem publicRecords_le {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (pr : Site.Programs N) (data : Epoch.Round.RecordData N) (hold : ∀ v, (pr v).program.publicNodes ≤ data.prior v)
    (test : N.Site → Prop) :
    localRecords N false pr.bankFields.prior pr.bankFields.payload test ≤ localRecords N false data.prior data.payload test := by
  unfold localRecords
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : test v
  · simp only [hv,ite_true,boxCost,recordCost,Bool.false_eq_true,ite_false,Nat.add_zero,Site.Programs.bankFields,
      Subdivision.publicProgramData]
    exact Nat.add_le_add_right (hold v) 1
  · simp [hv]

/-- All public row words in a tested region fit the same descriptor-mode local record count.
The payload function can be arbitrary in this mode. -/
theorem publicWords_le_localRecords {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (programs : N.Site → Site) (prior payload : N.Site → ℕ) (hold : ∀ v, (programs v).publicNodes ≤ prior v)
    (test : N.Site → Prop) :
    testedWidth (fun v => (Packet.fieldList Packet.record (programs v).rows).length) test ≤
      localRecords N false prior payload test := by
  have box : testedWidth (fun v => (Packet.fieldList Packet.record (programs v).rows).length) test ≤
      testedWidth (fun v => boxCost false (prior v) (payload v)) test := by
    unfold testedWidth
    apply Finset.sum_le_sum
    intro v _
    by_cases h : test v
    · simp only [h,ite_true,boxCost,recordCost,Bool.false_eq_true,ite_false]
      exact ((programs v).packetRows_le_publicNodes.trans (hold v)).trans (Nat.le_add_right ..)
    · simp [h]
  unfold localRecords
  omega

end Packing.Inherited

namespace PackedHistoryCircuit.Normalized

open Cover Crossing Shortening Shortening.Adaptive Packing Packing.Inherited InheritedBank Epoch.Round CellSparse
open scoped Classical
attribute [local instance] portFintype

variable {D m k d d' : ℕ} [NeZero D] {I P K Bin : Type} [Fintype P] [Fintype I] [Fintype Bin] [Field K]
    {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d} (s : Stage m Bin d' child) (e : PaidIdentity K D m)
    (q : s.Index e) (old : ∀ j, Site.Programs (child j).pack.layout) (data : ∀ j, RecordData (child j).pack.layout)
    {ns ne np : ℕ} (sites : (s.result e q).pack.layout.Site ↪ Fin ns) (edges : (s.result e q).pack.layout.Edge ↪ Fin ne)
    (ports : Fin k × P ↪ Fin np) (seeds : ((I → Deck (d'+1)) × Bin) → ℕ) (number : e.Entry → ℕ)

namespace Stage

/-- Every selected private program's public fields fit its own computed prior allowance. -/
theorem privatePrograms_public_le (hold : ∀ j v, (old j v).program.publicNodes ≤ (data j).prior v)
    (v : (s.result e q).pack.layout.Site) :
    (s.privatePrograms e q old sites edges ports seeds number v).program.publicNodes ≤ (s.bankRecordData e q data).prior v := by
  let previous := fun u : s.input.layout.Site => (old u.1 u.2).program
  let oldID := CutCircuit.denseRows (raw child).layout s.slot
  let cuts := fun u => Layer.orderedCuts s.input oldID ports u e s.label s.perm seeds s.orient (0,false) q edges
  have h := roundSites_public_charged e s.input s.label s.perm s.orient (0,false) q seeds number sites edges ports previous cuts
    (fun u => (data u.1).prior u.2) (fun u => (old u.1 u.2).size.trans (s.input_incoming u.1 u.2).symm)
    (fun u => hold u.1 u.2) (cuts_length_of_perm e s.input s.label s.perm s.orient (0,false) q seeds edges ports cuts
      oldID (fun u => Layer.ordered_perm s.input oldID ports u e s.label s.perm seeds s.orient (0,false) q edges)) v
  rcases v with oldV | fresh <;> exact h

/-- Expanded work and visits fit the separate payload allowance. No private factor
body is added to the public allowance in this estimate. -/
theorem privatePrograms_expanded_le (hold : ∀ j v, (old j v).program.expandedLoad ≤ (data j).payload v)
    (v : (s.result e q).pack.layout.Site) :
    (s.privatePrograms e q old sites edges ports seeds number v).program.expandedLoad ≤ (s.bankRecordData e q data).payload v := by
  let previous := fun u : s.input.layout.Site => (old u.1 u.2).program
  let oldID := CutCircuit.denseRows (raw child).layout s.slot
  let cuts := fun u => Layer.orderedCuts s.input oldID ports u e s.label s.perm seeds s.orient (0,false) q edges
  have h := roundSites_charged e s.input s.label s.perm s.orient (0,false) q seeds number sites edges ports previous cuts
    (fun u => (previous u).staticNodes) (fun u => (data u.1).payload u.2)
    (fun u => (old u.1 u.2).size.trans (s.input_incoming u.1 u.2).symm) (fun u => ⟨le_rfl,hold u.1 u.2⟩)
    (cuts_length_of_perm e s.input s.label s.perm s.orient (0,false) q seeds edges ports cuts oldID
      (fun u => Layer.ordered_perm s.input oldID ports u e s.label s.perm seeds s.orient (0,false) q edges)) v
  rcases v with oldV | fresh <;> exact h.2

end Stage

namespace Program

variable {rounds : ℕ} {A : ℕ → Type*} {B : Fin rounds → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
  {e : PaidIdentity K D m} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
  (F : Program (B := B) e view) (store : F.SaveNames) (rows : F.SiteRows) (number : e.Entry → ℕ)

omit [Field K] [NeZero D] in
set_option maxHeartbeats 1800000 in
private theorem nested_bankRelation (R : Site → ℕ → ℕ → Prop) (n : ℕ) (flat : Fin (k^n) → A 0)
    (data : ∀ i, RecordData (view 0 (flat i)).pack.layout) (pr : ∀ i, Site.Programs (view 0 (flat i)).pack.layout)
    (base : ∀ i v, R (pr i v).program ((data i).prior v) ((data i).payload v)) :
    ∀ v, let fields := parallelLeafData view n flat data
         let programs := nestedPrivatePrograms (fun x => (view 0 x).pack) n flat pr
         R (programs v).program (fields.prior v) (fields.payload v) := by
  induction n with
  | zero =>
    intro v fields programs
    exact base 0 v
  | succ n ih =>
    rintro ⟨j,v⟩
    exact ih (fun x => flat (copyIndex k n (j,x))) (fun x => data (copyIndex k n (j,x)))
      (fun x => pr (copyIndex k n (j,x))) (fun x => base _) v

/-- Actual retained and freshly installed public words are dominated pointwise by the
public-only prior field on the original selected normalized histogram. -/
theorem replayPrivatePrograms_public_le (n : ℕ) (hn : n ≤ rounds) (flat : Fin (k^n) → A 0)
    (data : ∀ i, RecordData (view 0 (flat i)).pack.layout) (pr : ∀ i, Site.Programs (view 0 (flat i)).pack.layout)
    (base : ∀ i v, (pr i v).program.publicNodes ≤ (data i).prior v) (q : F.FlatHist n hn flat) :
    let start := nestedPrivatePrograms (fun x => (view 0 x).pack) n flat pr
    let current := F.replayPrivatePrograms store rows number n hn (leavesEquiv k _ n flat) start q
    let fields := F.replayBankRecords store n hn flat data q
    ∀ v, (current v).program.publicNodes ≤ fields.prior v := by
  let R := fun (_ : ℕ) (s : Site) (p _ : ℕ) => s.publicNodes ≤ p
  exact F.replayPrivatePrograms_bankRelation store rows number R
    (fun i c q old fields h => (F.stage i c).privatePrograms_public_le e q old fields (rows.sites i c q)
      (store.number i c q) (rows.ports (i.val+1)) (rows.seeds i) number h) n hn flat data _
    (nested_bankRelation (view := view) (R 0) n flat data pr base) q

/-- The separate expanded field bounds the very same selected private programs. -/
theorem replayPrivatePrograms_expanded_le (n : ℕ) (hn : n ≤ rounds) (flat : Fin (k^n) → A 0)
    (data : ∀ i, RecordData (view 0 (flat i)).pack.layout) (pr : ∀ i, Site.Programs (view 0 (flat i)).pack.layout)
    (base : ∀ i v, (pr i v).program.expandedLoad ≤ (data i).payload v) (q : F.FlatHist n hn flat) :
    let start := nestedPrivatePrograms (fun x => (view 0 x).pack) n flat pr
    let current := F.replayPrivatePrograms store rows number n hn (leavesEquiv k _ n flat) start q
    let fields := F.replayBankRecords store n hn flat data q
    ∀ v, (current v).program.expandedLoad ≤ fields.payload v := by
  let R := fun (_ : ℕ) (s : Site) (_ p : ℕ) => s.expandedLoad ≤ p
  exact F.replayPrivatePrograms_bankRelation store rows number R
    (fun i c q old fields h => (F.stage i c).privatePrograms_expanded_le e q old fields (rows.sites i c q)
      (store.number i c q) (rows.ports (i.val+1)) (rows.seeds i) number h) n hn flat data _
    (nested_bankRelation (view := view) (R 0) n flat data pr base) q

/-- The full routed descriptor cap on the flattened true site programs, including their
published guards and cable-end records, is suitable as the input to the next epoch. -/
theorem flatPrivatePrograms_publicRecords {dst : ℕ} {L W X : ℝ} {H : ℕ} (C : Fin rounds → ℕ)
    (cert : ∀ i c, (F.stage i c).RecordFactor e (C i)) (T : ℕ) (hT : 0 < T)
    (flat : Fin (k^rounds) → A 0) (data : ∀ i, RecordData (view 0 (flat i)).pack.layout)
    (pr : ∀ i, Site.Programs (view 0 (flat i)).pack.layout)
    (base : ∀ i v, (pr i v).program.publicNodes ≤ (data i).prior v)
    (old : ∀ i, RecordsWithin (view 0 (flat i)) (data i) false T) (q : F.Hist flat)
    (out : SiteOutput (F.terminal flat q) dst L W X H) (tile) :
    let N := (flattenPack rounds (F.terminal flat q).pack).layout
    let current := F.flatPrivatePrograms store rows number flat pr q
    1+localRecords N false current.bankFields.prior current.bankFields.payload
      (fun v => reduceMove dst (out.routes.flatten.origin v) = tile) ≤ (1+H)*(1+∑ i, loadMultiplier e*C i*k)^rounds*T := by
  let current := F.flatPrivatePrograms store rows number flat pr q
  let p := F.terminal flat q
  let N := (flattenPack rounds p.pack).layout
  let fields := F.replayBankRecords store rounds le_rfl flat data q
  let test (v : N.Site) := reduceMove dst (out.routes.flatten.origin v) = tile
  have fit : ∀ v, (current v).program.publicNodes ≤ fields.prior v :=
    F.replayPrivatePrograms_public_le store rows number rounds le_rfl flat data pr base q
  let flatFields : RecordData N := ⟨fields.prior,fields.payload⟩
  have pub := publicRecords_le N current flatFields fit test
  have history := F.replayBankRecords_bound store C cert false T hT rounds le_rfl flat data old q
  have rounded := flat_output_record_bound p out fields false (Nat.mul_pos (pow_pos (Nat.add_pos_left (by decide) _) _) hT) history tile
  exact (Nat.add_le_add_left pub 1).trans (rounded.trans_eq (by ring))

end Program
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
