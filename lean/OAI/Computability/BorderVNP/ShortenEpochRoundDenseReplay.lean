import OAI.Computability.BorderVNP.ShortenEpochRoundDenseRecords
import OAI.Computability.BorderVNP.ShortenEpochRoundTrackedRecords
import OAI.Computability.BorderVNP.PackedHistoryDenseProgram

/-!
# Replaying actual retained records through a publicly normalized program

Each chosen dense histogram produces its own sewn fields on the actual
first, sorted input. Its saved result has a second specified public row
injection. The latter preserves every per-tile record count. Recursion
down the attained profile index uses its very child selectors, so separate
occurrences of a leaf may carry distinct input fields.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.Program

open BorderVNP.Crossing BorderVNP.Cover BorderVNP.Epoch BorderVNP.Epoch.Round BorderVNP.Packing
open BorderVNP.Shortening BorderVNP.Shortening.Adaptive Finset
open scoped Classical

attribute [local instance] portFintype

variable {D m k b : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I] [Fintype P] {bits : P → ℕ}
    {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
    {e : PaidIdentity K D m} {view : ∀ j, A j → PlacedPack D (Port k P j) (width bits k j) K I (depth j)}
    (F : Program (B := B) e view)

/-- The actual public destination row numbers and dense stored result at every histogram. -/
structure SaveNames where
  /-- Length of the actual public destination cable directory. -/
  capacity : ∀ (i : Fin b) (c : Fin k → A i.val), (F.stage i c).Index e → ℕ
  /-- Distinct actual physical cables have distinct directory rows. -/
  number : ∀ (i : Fin b) (c : Fin k → A i.val) (q : (F.stage i c).Index e),
    ((F.stage i c).result e q).pack.layout.Edge ↪ Fin (capacity i c q)
  /-- The saved physical state is precisely the sewn output reordered by these rows. -/
  stored : ∀ (i : Fin b) (c : Fin k → A i.val) (q : (F.stage i c).Index e),
    view (i.val+1) (F.advance i c q) = ((F.stage i c).result e q).dense (number i c q)

/-- Transfer the sewn fields through the second public ordering at save time. -/
noncomputable def saveData (S : F.SaveNames) (i : Fin b) (c : Fin k → A i.val) (q : (F.stage i c).Index e)
    (r : ∀ j, RecordData (view i.val (c j)).pack.layout) :
    RecordData (view (i.val+1) (F.advance i c q)).pack.layout :=
  transferData (S.stored i c q).symm
    ⟨(F.stage i c).resultPrior e q (fun j => (r j).prior),
      (F.stage i c).resultPayload e q (fun j => (r j).payload)⟩

set_option maxHeartbeats 2000000 in
/-- One selected dense step, including the actual second row sort on its saved result,
inherits the per-tile cap with its prepared record factor times the fan-in. -/
theorem savedRecordFactor (S : F.SaveNames) (i : Fin b) (c : Fin k → A i.val) (q : (F.stage i c).Index e)
    (r : ∀ j, RecordData (view i.val (c j)).pack.layout) (ex : Bool) {T C : ℕ}
    (hT : 0 < T) (cert : (F.stage i c).RecordFactor e C)
    (old : ∀ j, RecordsWithin (view i.val (c j)) (r j) ex T) :
    RecordsWithin (view (i.val+1) (F.advance i c q)) (F.saveData S i c q r) ex (C*k*T) := by
  let result := (F.stage i c).result e q
  let prior := (F.stage i c).resultPrior e q (fun j => (r j).prior)
  let payload := (F.stage i c).resultPayload e q (fun j => (r j).payload)
  have cap := cert q ex (fun j => (r j).prior) (fun j => (r j).payload) (T-1) (fun j t => by
    have ht := old j t
    have he : localRecords (view i.val (c j)).pack.layout ex (r j).prior (r j).payload
        (fun v => productAddress (depth i.val) ((view i.val (c j)).site v) = t) ≤ T-1 := by omega
    convert! he using 1)
  rw [show 1+(T-1) = T by omega] at cap
  apply (recordsWithin_transfer _ _ _ _).mpr
  intro t
  let test (v : result.pack.layout.Site) := productAddress (depth (i.val+1)) (result.site v) = t
  let f := portFintype (P := P) (k := k) (b := i.val+1)
  let counts (inst : Fintype (Fin k × Port k P i.val)) := 1+@localRecords D _ inst _ result.pack.layout ex prior payload test
  have same := congrArg counts (Subsingleton.elim f (instFintypeProd (Fin k) (Port k P i.val)))
  have raw : counts f ≤ C*k*T := same.le.trans (cap t)
  have sorted := @Names.localRecords_denseLayout D (S.capacity i c q) (Port k P (i.val+1)) (width bits k (i.val+1))
    result.pack.layout (S.number i c q) f ex prior payload test
  exact (congrArg (1+·) sorted).le.trans raw

/-- The actual ordinal in a normalized public profile tree above a flat input subarray. -/
abbrev FlatHist (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → A 0) :=
  (F.system.histories n hn (leavesEquiv k _ n flat)).Index

/-- Stored physical pack on the original history ordinal. -/
noncomputable def flatPack (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → A 0) (q : F.FlatHist n hn flat) :=
  view n ((F.system.layer n).state ((F.system.histories n hn (leavesEquiv k _ n flat)).term q))

set_option maxHeartbeats 2000000 in
/-- Evaluate the sewn public and expanded record maps on the exact selected dense histogram,
then store them using that histogram's actual second row numbering. -/
noncomputable def replayRecords (S : F.SaveNames) :
    ∀ (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → A 0)
      (_fields : ∀ i, RecordData (view 0 (flat i)).pack.layout) (q : F.FlatHist n hn flat),
      RecordData (F.flatPack n hn flat q).pack.layout
  | 0, _, _, fields, _ => fields 0
  | n+1, hn, flat, fields, q => by
    let i : Fin b := ⟨n,by omega⟩
    let sub (j : Fin k) (x : Fin (k^n)) := flat (copyIndex k n (j,x))
    let c (j : Fin k) := (F.system.layer n).state
      ((F.system.histories n (by omega) (leavesEquiv k _ n (sub j))).term (q.1 j))
    let r (j : Fin k) := replayRecords S n (by omega) (sub j) (fun x => fields (copyIndex k n (j,x))) (q.1 j)
    exact F.saveData S i c q.2 r

set_option maxHeartbeats 2000000 in
/-- The actual record fields on every normalized histogram, including its saved second
sort, satisfy the finite tree bound in either counting mode. -/
theorem replayRecords_bound (S : F.SaveNames) (C : Fin b → ℕ)
    (cert : ∀ i c, (F.stage i c).RecordFactor e (C i)) (ex : Bool) (T : ℕ) (hT : 0 < T)
    (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → A 0) (fields : ∀ i, RecordData (view 0 (flat i)).pack.layout)
    (old : ∀ i, RecordsWithin (view 0 (flat i)) (fields i) ex T) (q : F.FlatHist n hn flat) :
    RecordsWithin (F.flatPack n hn flat q) (F.replayRecords S n hn flat fields q) ex
      ((1+∑ i, C i*k)^n*T) := by
  induction n with
  | zero =>
    rw [pow_zero,one_mul,replayRecords]
    exact old 0
  | succ n ih =>
    let i : Fin b := ⟨n,by omega⟩
    let sub (j : Fin k) (x : Fin (k^n)) := flat (copyIndex k n (j,x))
    let c (j : Fin k) := (F.system.layer n).state
      ((F.system.histories n (by omega) (leavesEquiv k _ n (sub j))).term (q.1 j))
    let r (j : Fin k) := F.replayRecords S n (by omega) (sub j) (fun x => fields (copyIndex k n (j,x))) (q.1 j)
    let A := 1+∑ i, C i*k
    have hchild (j : Fin k) : RecordsWithin (view n (c j)) (r j) ex (A^n*T) :=
      ih (by omega) (sub j) (fun x => fields (copyIndex k n (j,x))) (fun x => old _) (q.1 j)
    have next := F.savedRecordFactor S i c q.2 r ex (Nat.mul_pos (pow_pos (Nat.add_pos_left (by decide : 0 < 1) _) _) hT)
      (cert i c) hchild
    have hci : C i*k ≤ A := (single_le_sum (f := fun j => C j*k) (fun _ _ => Nat.zero_le _) (mem_univ i)).trans
      (Nat.le_add_left _ _)
    intro t
    apply (next t).trans
    exact (Nat.mul_le_mul_right (A^n*T) hci).trans_eq (by dsimp only [A]; ring)

end PackedHistoryCircuit.Normalized.Program

end BorderVNP
end Computability
end OAI
