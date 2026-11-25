import OAI.Computability.BorderVNP.PackedBankPublicReplay
import OAI.Computability.BorderVNP.PackedBankFreshScalarBound
import OAI.Computability.BorderVNP.PackedBankInheritedScalarBounds
import OAI.Computability.BorderVNP.PackedHistoryCompilerRows

/-! # Local scalar words through the actual normalized private history

Every physical birth has a bound from its expanded tile and its old bin
population. A retained site's equality intervals use its current physical
extent. Both properties follow the original ordinal through the two dense
sorts, including zero-width intervals.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Cover Crossing Shortening Shortening.Adaptive Shortening.SeedIntervals Packing Packing.Inherited
  InheritedProfile InheritedBank Epoch Epoch.Round Diagonal.ExternalSew
open scoped Classical
attribute [local instance] portFintype
set_option maxHeartbeats 2000000

variable {D m k d d' : ℕ} [NeZero D] {I P K Bin : Type} [Fintype P] [Fintype I] [Fintype Bin] [Field K]
    {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d} (s : Stage m Bin d' child) (e : PaidIdentity K D m)
    (q : s.Index e) (old : ∀ j, Site.Programs (child j).pack.layout) (data : ∀ j, RecordData (child j).pack.layout)
    {ns ne np : ℕ} (sites : (s.result e q).pack.layout.Site ↪ Fin ns) (edges : (s.result e q).pack.layout.Edge ↪ Fin ne)
    (ports : Fin k × P ↪ Fin np) (seeds : ((I → Deck (d'+1)) × Bin) → ℕ) (number : e.Entry → ℕ)

namespace Stage

/-- The ordinary normalized record-factor certificate bounds every physical birth tile
from the expanded budgets of the actual children selected by the history. -/
theorem birthTileCap_of_children {C T : ℕ} (cert : s.RecordFactor e C) (hT : 0<T)
    (cap : ∀ j, RecordsWithin (child j) (data j) true T) :
    BirthTileCap e s.input s.label s.perm s.orient (0,false) q
      (fun v => productTileName d' ((s.result e q).site v)) (fun u => (data u.1).prior u.2)
      (fun u => (data u.1).payload u.2) (C*k*T) := by
  have bound := cert q true (fun j => (data j).prior) (fun j => (data j).payload) (T-1) (fun j t => by
    apply Nat.le_sub_of_add_le
    rw [Nat.add_comm]
    exact cap j t)
  rw [show 1+(T-1)=T by omega] at bound
  exact fun t => (Nat.le_add_left _ 1).trans (bound t)

/-- An attained normalized crossing preserves the scalar bound given by the
birth budget and the current site's extent, on retained and fresh sites alike. -/
theorem privatePrograms_scalarBound {M B U : ℕ} (hm : 0 < m)
    (cap : BirthTileCap e s.input s.label s.perm s.orient (0,false) q
      (fun v => productTileName d' ((s.result e q).site v)) (fun u => (data u.1).prior u.2)
      (fun u => (data u.1).payload u.2) M)
    (pool : ∀ a, count s.input.layout s.label a ≤ B) (limit : birthScalarLimit e M B ≤ U)
    (base : ∀ j v, let pr := (old j v).program
      pr.ScalarBound (max U (max 1 pr.size))) (v : (s.result e q).pack.layout.Site) :
    let pr := (s.privatePrograms e q old sites edges ports seeds number v).program
    pr.ScalarBound (max U (max 1 pr.size)) := by
  let previous := fun u : s.input.layout.Site => (old u.1 u.2).program
  let oldID := CutCircuit.denseRows (raw child).layout s.slot
  let cuts := fun u => Layer.orderedCuts s.input oldID ports u e s.label s.perm seeds s.orient (0,false) q edges
  rcases v with v | ⟨a,v⟩
  · let s₀ := previous v
    let inc := incoming (s.result e q).pack.layout (.inl v)
    have hin : s₀.incoming = incoming s.input.layout v := (old v.1 v.2).size.trans (s.input_incoming v.1 v.2).symm
    have cover := Layer.ordered_covers s.input oldID ports v e s.label s.perm seeds s.orient (0,false) q edges
    have retained := s₀.scalarBound_retain (base v.1 v.2) (fun z hz => (cover.oldFit z hz).trans_eq hin.symm) cover.newFit
    change (s₀.retain inc (cuts v)).ScalarBound (max U (max 1 (s₀.size+inc)))
    intro x hx
    have h := retained x hx
    change x.2 ≤ max (max U (max 1 s₀.size)) (max 1 (s₀.size+inc)) at h
    omega
  · have h := roundSites_fresh_scalarBound e s.input s.label s.perm s.orient (0,false) q _ _ _ M cap hm a
      sites edges ports seeds number B pool previous cuts v
    intro pr x hx
    exact (h x hx).trans (limit.trans (le_max_left ..))

end Stage

namespace Program

variable {b : ℕ} {A : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
  {e : PaidIdentity K D m} {view : ∀ n, A n → PlacedPack D (Port k P n) (width bits k n) K I (depth n)}
  (F : Program (B := B) e view) (store : F.SaveNames) (rows : F.SiteRows) (number : e.Entry → ℕ)

omit [NeZero D] in
/-- Each stage's ordinary expanded tile bound fits the complete epoch's cumulative
factor, even when that stage occurs on a selected inner branch of the history. -/
theorem stageCapacity_le (C : Fin b → ℕ) (T : ℕ) (i : Fin b) :
    C i*k*((1+∑ j, loadMultiplier e*C j*k)^i.val*T) ≤ (1+∑ j, loadMultiplier e*C j*k)^b*T := by
  let f := 1+∑ j, loadMultiplier e*C j*k
  have hf : 0<f := Nat.add_pos_left (by decide : 0<1) _
  have hm : 0<loadMultiplier e := by unfold loadMultiplier; omega
  have step := (Finset.single_le_sum (f := fun j => loadMultiplier e*C j*k) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)).trans (Nat.le_add_left _ 1)
  have h : C i*k ≤ f := (Nat.mul_le_mul_right k (Nat.le_mul_of_pos_left _ hm)).trans step
  have pow := Nat.pow_le_pow_right hf (Nat.succ_le_of_lt i.isLt)
  calc
    C i*k*(f^i.val*T) ≤ f*(f^i.val*T) := Nat.mul_le_mul_right _ h
    _ = f^(i.val+1)*T := by rw [pow_succ',Nat.mul_assoc]
    _ ≤ f^b*T := Nat.mul_le_mul_right _ pow

set_option maxHeartbeats 2400000 in
/-- Scalar bounds on the genuinely executed programs of every selected normalized
branch. The expanded tile budget is derived recursively from the original leaves;
the locality premise bounds the population of each selected bin on those tiles. -/
theorem replayPrivatePrograms_scalarBound (hm : 0 < m) (C : Fin b → ℕ) (cert : ∀ i c, (F.stage i c).RecordFactor e (C i))
    (T : ℕ) (hT : 0<T) (L V U : ℕ)
    (large : (1+∑ j, loadMultiplier e*C j*k)^b*T ≤ L)
    (pool : ∀ i c (q : (F.stage i c).Index e) (prior payload : (F.stage i c).input.layout.Site → ℕ),
      let s := F.stage i c
      BirthTileCap e s.input s.label s.perm s.orient (0,false) q
        (fun v => productTileName (depth (i.val+1)) ((s.result e q).site v)) prior payload L →
      ∀ a, count s.input.layout s.label a ≤ V*L)
    (limit : birthScalarLimit e L (V*L) ≤ U) (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → A 0)
    (data : ∀ j, RecordData (view 0 (flat j)).pack.layout) (leafCap : ∀ j, RecordsWithin (view 0 (flat j)) (data j) true T)
    (initial : Site.Programs (parallelLeaves (fun a => (view 0 a).pack) n (leavesEquiv k _ n flat)).layout)
    (base : ∀ v, let s := (initial v).program
      s.ScalarBound (max U (max 1 s.size))) (q : F.FlatHist n hn flat) :
    ∀ v, let pr := (F.replayPrivatePrograms store rows number n hn (leavesEquiv k _ n flat) initial q v).program
         pr.ScalarBound (max U (max 1 pr.size)) := by
  induction n with
  | zero => exact base
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
    let factor := 1+∑ j, loadMultiplier e*C j*k
    have child (j : Fin k) : RecordsWithin (view n (c j)) (fields j) true (factor^n*T) :=
      F.replayBankRecords_bound store C cert true T hT n (by omega) (sub j) (subData j) (fun x => leafCap _) (q.1 j)
    have hp : 0<factor^n*T := Nat.mul_pos (pow_pos (Nat.add_pos_left (by decide : 0<1) _) _) hT
    let s := F.stage i c
    have cap := s.birthTileCap_of_children e q.2 fields (cert i c) hp child
    have full : BirthTileCap e s.input s.label s.perm s.orient (0,false) q.2
        (fun v => productTileName (depth (i.val+1)) ((s.result e q.2).site v)) (fun u => (fields u.1).prior u.2)
        (fun u => (fields u.1).payload u.2) L :=
      fun t => (cap t).trans ((stageCapacity_le (e := e) C T i).trans large)
    have good (j : Fin k) := ih (by omega) (sub j) (subData j) (fun x => leafCap _) (src j) (fun u => base ⟨j,u⟩) (q.1 j)
    exact F.savePrivatePrograms_forall store rows number (fun pr => pr.ScalarBound (max U (max 1 pr.size))) i c q.2 old
      (s.privatePrograms_scalarBound e q.2 old fields (rows.sites i c q.2) (store.number i c q.2) (rows.ports (i.val+1))
        (rows.seeds i) number hm full (pool i c q.2 _ _ full) limit good)

end Program
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
