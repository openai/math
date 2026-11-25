import OAI.Computability.BorderVNP.PackedHistoryPrivateSites

/-! # Coupled replay of site programs and their numerical record fields

Each physical program and its bank record use the same child tuple, public
histogram ordinal and destination cable ordering. A relation on the program
and its own two scalar fields therefore propagates at every physical host.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.Program

open Cover Crossing Shortening Shortening.Adaptive Packing Packing.Inherited Epoch.Round Diagonal.ExternalSew
open scoped Classical
attribute [local instance] portFintype

variable {D m k b : ℕ} [NeZero D] {I P K : Type} [Fintype I] [Fintype P] [Field K]
  {bits : P → ℕ} {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
  {e : PaidIdentity K D m} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
  (F : Program (B := B) e view) (store : F.SaveNames) (rows : F.SiteRows) (number : e.Entry → ℕ)

/-- Put each flat input occurrence's two fields at its own sites in the parallel leaf network. -/
noncomputable def parallelLeafData (view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)) :
    ∀ (n : ℕ) (flat : Fin (k^n) → A 0) (_data : ∀ j, RecordData (view 0 (flat j)).pack.layout),
    RecordData (parallelLeaves (fun a => (view 0 a).pack) n (leavesEquiv k _ n flat)).layout
  | 0, _, data => data 0
  | n+1, flat, data =>
    let sub (j : Fin k) := parallelLeafData view n (fun x => flat (copyIndex k n (j,x))) (fun x => data (copyIndex k n (j,x)))
    ⟨fun v => (sub v.1).prior v.2,fun v => (sub v.1).payload v.2⟩

omit [NeZero D] [Field K] in
private theorem carry_related {Q : Type} {widths : Q → ℕ} {d E : ℕ} {fin fin' : Fintype Q}
    (p saved : PlacedPack D Q widths K I d) (edge : p.pack.layout.Edge ↪ Fin E) (h : saved = p.dense edge)
    (old : @Site.Programs D Q fin widths p.pack.layout) (data : RecordData p.pack.layout)
    (R : Site → ℕ → ℕ → Prop) (good : ∀ v, R (old v).program (data.prior v) (data.payload v)) :
    let pr := carryPrivatePrograms p saved edge h (fin' := fin') old
    let fields := transferData h.symm ⟨data.prior,data.payload⟩
    ∀ v, R (pr v).program (fields.prior v) (fields.payload v) := by subst saved; exact good

variable (R : ℕ → Site → ℕ → ℕ → Prop)

/-- A relation between the newly installed program and the fields on that same site
survives the program's actual second dense save. -/
theorem savePrivatePrograms_bankRelation (i : Fin b) (c : Fin k → A i.val) (q : (F.stage i c).Index e)
    (old : ∀ j, Site.Programs (view i.val (c j)).pack.layout)
    (data : ∀ j, RecordData (view i.val (c j)).pack.layout)
    (good : ∀ v, let s := F.stage i c
      let pr := s.privatePrograms e q old (rows.sites i c q) (store.number i c q) (rows.ports (i.val+1)) (rows.seeds i) number
      let fields := s.bankRecordData e q data
      R (i.val+1) (pr v).program (fields.prior v) (fields.payload v)) :
    let pr := F.savePrivatePrograms store rows number i c q old
    let fields := F.saveBankData store i c q data
    ∀ v, R (i.val+1) (pr v).program (fields.prior v) (fields.payload v) := by
  exact carry_related _ _ _ (store.stored i c q) _ _ _ good

set_option maxHeartbeats 2000000 in
/-- Follow the literal program and numerical record recursions on the original flat
history ordinal. The relation may depend on both scalar fields of each physical site. -/
theorem replayPrivatePrograms_bankRelation
    (step : ∀ (i : Fin b) (c : Fin k → A i.val) (q : (F.stage i c).Index e)
      (old : ∀ j, Site.Programs (view i.val (c j)).pack.layout)
      (data : ∀ j, RecordData (view i.val (c j)).pack.layout),
      (∀ j v, R i.val (old j v).program ((data j).prior v) ((data j).payload v)) →
      ∀ v, let s := F.stage i c
           let pr := s.privatePrograms e q old (rows.sites i c q) (store.number i c q) (rows.ports (i.val+1)) (rows.seeds i) number
           let fields := s.bankRecordData e q data
           R (i.val+1) (pr v).program (fields.prior v) (fields.payload v))
    (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → A 0)
    (data : ∀ j, RecordData (view 0 (flat j)).pack.layout)
    (initial : Site.Programs (parallelLeaves (fun a => (view 0 a).pack) n (leavesEquiv k _ n flat)).layout)
    (base : ∀ v, let fields := parallelLeafData view n flat data
      R 0 (initial v).program (fields.prior v) (fields.payload v)) (q : F.FlatHist n hn flat) :
    let pr := F.replayPrivatePrograms store rows number n hn (leavesEquiv k _ n flat) initial q
    let fields := F.replayBankRecords store n hn flat data q
    ∀ v, R n (pr v).program (fields.prior v) (fields.payload v) := by
  induction n with
  | zero =>
    intro pr fields v
    change R 0 (initial v).program ((data 0).prior v) ((data 0).payload v)
    exact base v
  | succ n ih =>
    let i : Fin b := ⟨n,Nat.lt_of_succ_le hn⟩
    let sub (j : Fin k) (x : Fin (k^n)) := flat (copyIndex k n (j,x))
    let a (j : Fin k) := leavesEquiv k _ n (sub j)
    let c (j : Fin k) := RowTrace.state F.system n (by omega) (a j) (q.1 j)
    let networks := fun j : Fin k => (parallelLeaves (fun a => (view 0 a).pack) n (a j)).layout
    let src (j : Fin k) (v : (networks j).Site) := (initial ⟨j,v⟩).castWidth
      ((incoming_instances _ _).trans (Inherited.Parallel.incoming_eq networks j v))
    let subData (j : Fin k) (x : Fin (k^n)) := data (copyIndex k n (j,x))
    let old (j : Fin k) := F.replayPrivatePrograms store rows number n (by omega) (a j) (src j) (q.1 j)
    let fields (j : Fin k) := F.replayBankRecords store n (by omega) (sub j) (subData j) (q.1 j)
    have good (j : Fin k) (v) : R n (old j v).program ((fields j).prior v) ((fields j).payload v) :=
      ih (by omega) (sub j) (subData j) (src j) (fun u => base ⟨j,u⟩) (q.1 j) v
    exact F.savePrivatePrograms_bankRelation store rows number R i c q.2 old fields (step i c q.2 old fields good)

end PackedHistoryCircuit.Normalized.Program

end BorderVNP
end Computability
end OAI
