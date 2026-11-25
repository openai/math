import OAI.Computability.BorderVNP.PackedBankInheritedDenseCharges
import OAI.Computability.BorderVNP.ShortenEpochRoundDenseReplay

/-! # Cumulative bank records on normalized physical histories

Each saved histogram carries the bank fields from its selected dense sewing step.
The destination cable ordering preserves their tile counts. Replaying the child
ordinals of a flat history thus gives bounds for the public and expanded records
on its actual stored pack.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.Program

open BorderVNP.Crossing BorderVNP.Cover BorderVNP.Epoch BorderVNP.Epoch.Round BorderVNP.Packing
open BorderVNP.Shortening BorderVNP.Shortening.Adaptive InheritedBank Finset
open scoped Classical

attribute [local instance] portFintype

variable {D m k b : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I] [Fintype P] {bits : P → ℕ}
    {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {e : PaidIdentity K D m} {view : ∀ j, A j → PlacedPack D (Port k P j) (width bits k j) K I (depth j)}
    (F : Program (B := B) e view)

/-- Store the selected histogram's cumulative bank fields under its second dense row ordering. -/
noncomputable def saveBankData (S : F.SaveNames) (i : Fin b) (c : Fin k → A i.val) (q : (F.stage i c).Index e)
    (data : ∀ j, RecordData (view i.val (c j)).pack.layout) :
    RecordData (view (i.val+1) (F.advance i c q)).pack.layout :=
  let sewn := (F.stage i c).bankRecordData e q data
  transferData (S.stored i c q).symm ⟨sewn.prior, sewn.payload⟩

set_option maxHeartbeats 2000000 in
/-- The destination cable ordering preserves the cumulative bound on every tile. -/
theorem savedBankData_within (S : F.SaveNames) (i : Fin b) (c : Fin k → A i.val) (q : (F.stage i c).Index e)
    (data : ∀ j, RecordData (view i.val (c j)).pack.layout) (ex : Bool) {T C : ℕ}
    (hT : 0 < T) (cert : (F.stage i c).RecordFactor e C)
    (old : ∀ j, RecordsWithin (view i.val (c j)) (data j) ex T) :
    RecordsWithin (view (i.val+1) (F.advance i c q)) (F.saveBankData S i c q data) ex (loadMultiplier e*C*k*T) := by
  let result := (F.stage i c).result e q
  let sewn := (F.stage i c).bankRecordData e q data
  have cap := (F.stage i c).bankRecordData_within e q data cert ex T hT old
  let tested (f : Fintype (Fin k × Port k P i.val)) :=
    @RecordsWithin D _ _ _ f _ _ _ result sewn ex (loadMultiplier e*C*k*T)
  have raw := (congrArg tested (Subsingleton.elim (portFintype (P := P) (k := k) (b := i.val+1))
    (instFintypeProd (Fin k) (Port k P i.val)))).mpr cap
  apply (recordsWithin_transfer _ _ _ _).mpr
  intro t
  have sorted := @Names.localRecords_denseLayout D (S.capacity i c q) (Port k P (i.val+1)) (width bits k (i.val+1))
    result.pack.layout (S.number i c q) portFintype ex sewn.prior sewn.payload
    (fun v => productAddress (depth (i.val+1)) (result.site v) = t)
  exact (congrArg (1+·) sorted).le.trans (raw t)

set_option maxHeartbeats 2000000 in
/-- Follow the original child ordinals, sew their bank fields, and save at the selected destination rows. -/
noncomputable def replayBankRecords (S : F.SaveNames) :
    ∀ (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → A 0)
      (_fields : ∀ i, RecordData (view 0 (flat i)).pack.layout) (q : F.FlatHist n hn flat),
      RecordData (F.flatPack n hn flat q).pack.layout
  | 0, _, _, fields, _ => fields 0
  | n+1, hn, flat, fields, q => by
    let i : Fin b := ⟨n, by omega⟩
    let sub (j : Fin k) (x : Fin (k^n)) := flat (copyIndex k n (j,x))
    let c (j : Fin k) := (F.system.layer n).state
      ((F.system.histories n (by omega) (leavesEquiv k _ n (sub j))).term (q.1 j))
    let data (j : Fin k) := replayBankRecords S n (by omega) (sub j)
      (fun x => fields (copyIndex k n (j,x))) (q.1 j)
    exact F.saveBankData S i c q.2 data

set_option maxHeartbeats 2000000 in
/-- Per-tile cap for the cumulative bank fields of every attained dense histogram. -/
theorem replayBankRecords_bound (S : F.SaveNames) (C : Fin b → ℕ)
    (cert : ∀ i c, (F.stage i c).RecordFactor e (C i)) (ex : Bool) (T : ℕ) (hT : 0 < T)
    (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → A 0) (fields : ∀ i, RecordData (view 0 (flat i)).pack.layout)
    (old : ∀ i, RecordsWithin (view 0 (flat i)) (fields i) ex T) (q : F.FlatHist n hn flat) :
    RecordsWithin (F.flatPack n hn flat q) (F.replayBankRecords S n hn flat fields q) ex
      ((1+∑ i, loadMultiplier e*C i*k)^n*T) := by
  induction n with
  | zero =>
    rw [pow_zero, one_mul, replayBankRecords]
    exact old 0
  | succ n ih =>
    let i : Fin b := ⟨n, by omega⟩
    let sub (j : Fin k) (x : Fin (k^n)) := flat (copyIndex k n (j,x))
    let c (j : Fin k) := (F.system.layer n).state
      ((F.system.histories n (by omega) (leavesEquiv k _ n (sub j))).term (q.1 j))
    let data (j : Fin k) := F.replayBankRecords S n (by omega) (sub j)
      (fun x => fields (copyIndex k n (j,x))) (q.1 j)
    let factor := 1+∑ i, loadMultiplier e*C i*k
    have child (j : Fin k) : RecordsWithin (view n (c j)) (data j) ex (factor^n*T) :=
      ih (by omega) (sub j) (fun x => fields (copyIndex k n (j,x))) (fun x => old _) (q.1 j)
    have pos : 0 < factor^n*T := Nat.mul_pos (pow_pos (Nat.add_pos_left (by decide : 0 < 1) _) _) hT
    have saved := F.savedBankData_within S i c q.2 data ex pos (cert i c) child
    have stage_le : loadMultiplier e*C i*k ≤ factor :=
      (single_le_sum (f := fun j => loadMultiplier e*C j*k) (fun _ _ => Nat.zero_le _) (mem_univ i)).trans
        (Nat.le_add_left _ _)
    intro t
    apply (saved t).trans
    exact (Nat.mul_le_mul_right (factor^n*T) stage_le).trans_eq (by dsimp only [factor]; ring)

end PackedHistoryCircuit.Normalized.Program

end BorderVNP
end Computability
end OAI
