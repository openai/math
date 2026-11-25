import OAI.Computability.BorderVNP.ShortenEpochRoundReplay

/-!
# Exact agreement of physical and record-carrying histograms

The original and decorated programs have one-to-one public histograms.
At each node the child correspondence merely transports the selector index
through equality of the actual child tuple. Consequently the original and
decorated physical layouts agree on the corresponding history.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Adaptive.Program

open BorderVNP.Crossing BorderVNP.Cover BorderVNP.Packing BorderVNP.Epoch.Round
open scoped Classical

variable {D m k b : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I] {bits : P → ℕ}
  {states : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
  {view : ∀ j, states j → PlacedPack D (Port k P j) (width bits k j) K I (depth j)}
  {e : PaidIdentity K D m} (F : Program (B := B) e view) (direct : F.Direct)

/-- Original and record-carrying histories with the exact same underlying state. -/
structure RecordMatch (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → states 0)
    (tracked : Fin (k^n) → Tracked view 0) where
  /-- A bijection of the attained joint profile choices. -/
  index : (F.system.histories n hn (leavesEquiv k _ n flat)).Index ≃
    ((F.withRecords direct).system.histories n hn (leavesEquiv k _ n tracked)).Index
  /-- Forgetting the carried records recovers the same physical state. -/
  stored : ∀ i, (((F.withRecords direct).system.layer n).state
    (((F.withRecords direct).system.histories n hn (leavesEquiv k _ n tracked)).term (index i))).1 =
    (F.system.layer n).state ((F.system.histories n hn (leavesEquiv k _ n flat)).term i)

private theorem advance_cast (i : Fin b) {c u : Fin k → states i.val} (h : c = u)
    (q : (F.step i c).Index e) :
    F.advance i u ((Equiv.cast (congrArg (fun a => (F.step i a).Index e) h)) q) = F.advance i c q := by
  cases h; rfl

set_option maxHeartbeats 2500000 in
/-- Bijection from the given flat input tuple's actual histogram tree to the same histogram
tree with record fields carried separately at each input occurrence. -/
noncomputable def matchRecords : ∀ (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → states 0)
    (tracked : Fin (k^n) → Tracked view 0), (∀ i, (tracked i).1 = flat i) → F.RecordMatch direct n hn flat tracked
  | 0, _, flat, tracked, h => ⟨Equiv.refl _,fun _ => h 0⟩
  | n+1, hn, flat, tracked, h => by
    let j : Fin b := ⟨n,by omega⟩
    let G := F.withRecords direct
    let old (i : Fin k) := F.system.histories n (by omega)
      (leavesEquiv k _ n (fun x => flat (copyIndex k n (i,x))))
    let fresh (i : Fin k) := G.system.histories n (by omega)
      (leavesEquiv k _ n (fun x => tracked (copyIndex k n (i,x))))
    let sub (i : Fin k) := matchRecords n (by omega) (fun x => flat (copyIndex k n (i,x)))
      (fun x => tracked (copyIndex k n (i,x))) (fun x => h _)
    let tuple : (∀ i, (old i).Index) ≃ (∀ i, (fresh i).Index) := Equiv.piCongrRight (fun i => (sub i).index)
    let c (x : ∀ i, (old i).Index) (i : Fin k) := (F.system.layer n).state ((old i).term (x i))
    let u (y : ∀ i, (fresh i).Index) (i : Fin k) := ((G.system.layer n).state ((fresh i).term (y i))).1
    have ha (x : ∀ i, (old i).Index) : c x = u (tuple x) := funext (fun i => ((sub i).stored (x i)).symm)
    let fiber (x : ∀ i, (old i).Index) : (F.step j (c x)).Index e ≃ (F.step j (u (tuple x))).Index e :=
      Equiv.cast (congrArg (fun a => (F.step j a).Index e) (ha x))
    let whole : (Σ x : ∀ i, (old i).Index, (F.step j (c x)).Index e) ≃
        (Σ y : ∀ i, (fresh i).Index, (F.step j (u y)).Index e) := Equiv.sigmaCongr tuple fiber
    refine ⟨whole,?_⟩
    rintro ⟨x,q⟩
    exact F.advance_cast j (ha x) q

/-- The actual executed network is equal on corresponding histograms at every stage. -/
theorem executed_match {n : ℕ} {hn : n ≤ b} {flat : Fin (k^n) → states 0} {tracked : Fin (k^n) → Tracked view 0}
    (matchR : F.RecordMatch direct n hn flat tracked)
    (i : (F.system.histories n hn (leavesEquiv k _ n flat)).Index) :
    (F.withRecords direct).executed n (((F.withRecords direct).system.histories n hn
      (leavesEquiv k _ n tracked)).term (matchR.index i)) =
      F.executed n ((F.system.histories n hn (leavesEquiv k _ n flat)).term i) := by
  rw [(F.withRecords direct).executed_eq_state (F.withRecords_direct direct),F.executed_eq_state direct]
  exact congrArg (view n) (matchR.stored i)

/-- At the final depth, corresponding original and decorated histogram outputs are the
same physical pack, including all site and tensor data. -/
theorem terminal_match {flat : Fin (k^b) → states 0} {tracked : Fin (k^b) → Tracked view 0}
    (matchR : F.RecordMatch direct b le_rfl flat tracked) (i : F.Hist flat) :
    (F.withRecords direct).terminal tracked (matchR.index i) = F.terminal flat i := by
  exact F.executed_match direct matchR i

end Shortening.Adaptive.Program

end BorderVNP
end Computability
end OAI
