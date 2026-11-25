import OAI.Computability.BorderVNP.DiagonalExternalSewEnriched
import OAI.Computability.BorderVNP.ShortenEpochRoundDenseExecutionRecords

/-! # Original box data at its retained site in the selected sorted history

The two record fields on an old vertex are inherited exactly. This follows
the same successive site embeddings that identify an original processor box
at the terminal public tile. Newly created histogram vertices do not alter
the descriptor or payload of any of these retained boxes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Packing CellEntries
open PackedHistoryCircuit.Normalized
open scoped Classical
attribute [local instance] portFintype

section Abstract

variable {D m k b : ℕ} [NeZero D] {K I P : Type} [Field K] [Fintype I] [Fintype P] {bits : P → ℕ}
variable {e : PaidIdentity K D m}

/-- The old descriptor and private payload at a particular site. -/
def boxFields {D : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits}
    (data : RecordData N) (v : N.Site) : ℕ × ℕ := (data.prior v,data.payload v)

omit [NeZero D] [Fintype P] [Field K] in
private theorem afterSave {d rows : ℕ} (result dst : PlacedPack D P bits K I d)
    (number : result.pack.layout.Edge ↪ Fin rows) (eq : dst = result.dense number)
    (data : RecordData (result.dense number).pack.layout) (v : result.pack.layout.Site) :
    let saved : Storage result.pack.layout dst.pack.layout := by rw [eq]; exact Storage.dense _ number
    boxFields (transferData eq.symm data) (saved.site v) = boxFields data v := by
  subst dst
  rfl

variable {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
variable {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
variable (F : PackedHistoryCircuit.Normalized.Program (B := B) e view) (names : F.SaveNames)

omit [Fintype P] in
set_option maxHeartbeats 1200000 in
/-- A retained site of any child carries both of its original fields after
the incoming sort, histogram replacement, and outgoing sort. -/
theorem saveFields (i : Fin b) (c : Fin k → A i.val) (q : (F.stage i c).Index e)
    (fields : ∀ j, RecordData (view i.val (c j)).pack.layout) (j : Fin k) (v : (view i.val (c j)).pack.layout.Site) :
    boxFields (F.saveData names i c q fields)
      ((namesStorage F names i c q).site ((normalizedStage e (F.stage i c) q).site ⟨j,v⟩)) = boxFields (fields j) v := by
  let s := F.stage i c
  let y := s.result e q
  let r : RecordData (y.dense (names.number i c q)).pack.layout :=
    ⟨s.resultPrior e q (fun j => (fields j).prior),s.resultPayload e q (fun j => (fields j).payload)⟩
  exact afterSave y (view (i.val+1) (F.advance i c q)) _ (names.stored i c q) r
    ((normalizedStage e s q).site ⟨j,v⟩)

omit [Fintype P] in
set_option maxHeartbeats 1500000 in
/-- The retained field pair at every nested original vertex, traced through
the same concrete sorted choices as the terminal tensor. -/
theorem nestedFields (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → A 0)
    (fields : ∀ i, RecordData (view 0 (flat i)).pack.layout) (q : F.FlatHist n hn flat)
    (v : (parallelLeaves (fun x => (view 0 x).pack) n (leavesEquiv k (A 0) n flat)).layout.Site) :
    let z := originalNames (fun x => (view 0 x).pack) n flat v
    boxFields (F.replayRecords names n hn flat fields q)
      ((normalizedAncestry F (namesStorage F names) n hn (leavesEquiv k (A 0) n flat) q).site v) =
      boxFields (fields z.1) z.2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases v with ⟨j,v⟩
    let i : Fin b := ⟨n,by omega⟩
    let sub (j : Fin k) (x : Fin (k^n)) := flat (copyIndex k n (j,x))
    let data (j : Fin k) := fun x => fields (copyIndex k n (j,x))
    let c (j : Fin k) := (F.system.layer n).state
      ((F.system.histories n (by omega) (leavesEquiv k _ n (sub j))).term (q.1 j))
    let r (j : Fin k) := F.replayRecords names n (by omega) (sub j) (data j) (q.1 j)
    let h := normalizedAncestry F (namesStorage F names) n (by omega) (leavesEquiv k _ n (sub j)) (q.1 j)
    exact (saveFields F names i c q.2 r j (h.site v)).trans (ih (by omega) (sub j) (data j) (q.1 j) v)

omit [Fintype P] in
set_option maxHeartbeats 1500000 in
/-- On the native terminal histogram the fields at the original row-major
leaf host agree exactly with the incoming original fields. -/
theorem flatFields (flat : Fin (k^b) → A 0) (fields : ∀ i, RecordData (view 0 (flat i)).pack.layout)
    (q : F.Hist flat) (i : Fin (k^b)) (v : (view 0 (flat i)).pack.layout.Site) :
    boxFields (F.replayRecords names b le_rfl flat fields q)
      ((normalizedHosts F (namesStorage F names) flat q).site ⟨i,v⟩) = boxFields (fields i) v := by
  let order := originalNames (fun x => (view 0 x).pack) b flat
  let z : (parallelPacks fun i => (view 0 (flat i)).pack).layout.Site := ⟨i,v⟩
  have he := nestedFields F names b le_rfl flat fields q (order.symm z)
  change _ = boxFields (fields (order (order.symm z)).1) (order (order.symm z)).2 at he
  rw [order.apply_symm_apply] at he
  exact he

omit [NeZero D] [Fintype P] [Field K] in
private theorem atPackEq {p y : Pack D P bits K} (eq : p = y) (data : RecordData p.layout)
    (v : p.layout.Site) :
    boxFields (cast (congrArg (fun z => RecordData z.layout) eq) data)
      ((Retains.ofEq (congrArg Pack.layout eq)).site v) = boxFields data v := by cases eq; rfl

omit [NeZero D] [Fintype P] [Field K] in
private theorem atPlacedEq {d : ℕ} {p y : PlacedPack D P bits K I d} (eq : p = y)
    (data : RecordData p.pack.layout) (v : p.pack.layout.Site) :
    boxFields (cast (congrArg (fun z => RecordData z.pack.layout) eq) data)
      ((Retains.ofEq (congrArg (fun z => z.pack.layout) eq)).site v) = boxFields data v := by cases eq; rfl

end Abstract

variable {D m d : ℕ} [NeZero D] {K P : Type} [Field K] {bits : P → ℕ} {e : PaidIdentity K D m}
variable {S : PackedHistoryCircuit.Normalized.SiteSchedule e} {A : ℕ → Type*}
variable {view : S.GeometricView d P bits A} (F : S.EnrichedProgram d view) (names : F.SaveNames)
variable {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
variable (flat : Fin (S.fanIn^S.rounds) → A 0) (initial : ∀ i, InitialSites (view 0 (flat i)) S.budget S.radius_pos)
variable (original : ∀ i, (initial i).pack = input i) (fields : ∀ i, RecordData (input i).layout)

/-- The original pair of fields at a retained vertex is preserved by the
particular geodesic subdivision installed at this public leaf. -/
theorem installedFields (i : Fin (S.fanIn^S.rounds)) (v : (input i).layout.Site) :
    let data := cast (congrArg (fun z : Pack D P bits K => RecordData z.layout) (original i).symm) (fields i)
    boxFields ((initial i).installedData data) ((enrichedInstalledHosts flat initial original i).site v) =
      boxFields (fields i) v := by
  let f := cast (congrArg (fun z : Pack D P bits K => RecordData z.layout) (original i).symm) (fields i)
  let orig := Retains.ofEq (congrArg Pack.layout (original i).symm)
  let r := (initial i).routes
  let stored : RecordData (r.initialPlacedPack S.radius_pos).pack.layout :=
    ⟨Sum.elim f.prior (fun _ => 0),Sum.elim f.payload (fun _ => 0)⟩
  exact (atPlacedEq (initial i).realizes.symm stored (Sum.inl (orig.site v))).trans
    (atPackEq (original i).symm (fields i) v)

set_option maxHeartbeats 1000000 in
/-- Every original bottom-site descriptor and payload reaches its real
retained host in the normalized histogram, even when the state carries
additional private-box metadata and public circuit words. -/
theorem originalFields (q : F.Hist flat) (i : Fin (S.fanIn^S.rounds)) (v : (input i).layout.Site) :
    let data (i) := cast (congrArg (fun z : Pack D P bits K => RecordData z.layout) (original i).symm) (fields i)
    boxFields (F.siteRecords names flat initial data q) ((enrichedHistoryHosts F flat initial original names q).site ⟨i,v⟩) =
      boxFields (fields i) v := by
  let data (i) := cast (congrArg (fun z : Pack D P bits K => RecordData z.layout) (original i).symm) (fields i)
  let root := (enrichedInstalledHosts flat initial original i).site v
  exact (flatFields F names flat (fun j => (initial j).installedData (data j)) q i root).trans
    (installedFields flat initial original fields i v)

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
