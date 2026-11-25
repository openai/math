import OAI.Computability.BorderVNP.ShortenEpochRoundRecordTree
import OAI.Computability.BorderVNP.ShortenStageRecords
import OAI.Computability.BorderVNP.ShortenSiteProgram

/-!
# Installing actual records at every chosen histogram

Carry each box's inherited descriptor history and extra payload as part of
the physical state. Distinct occurrences of the same starting tensor may
carry different input records. The choice of physical step ignores these
extra fields and keeps the same measurement and record factor. Its successor
uses exactly the sewn record maps of that selected histogram.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch.Round

open BorderVNP.Shortening BorderVNP.Shortening.Adaptive BorderVNP.Cover BorderVNP.Crossing Finset
open scoped Classical

attribute [local instance] portFintype

variable {I P : Type} [Fintype I] {D d : ℕ} {K : Type*} {bits : P → ℕ}

/-- Transfer record fields when the physical pack is stored with an equal representation. -/
def transferData {p y : PlacedPack D P bits K I d} (h : p = y) (data : RecordData p.pack.layout) :
    RecordData y.pack.layout := h ▸ data

/-- A relabelling by pack equality preserves every record-cap test. -/
theorem recordsWithin_transfer [Fintype P] {p y : PlacedPack D P bits K I d} (h : p = y)
    (data : RecordData p.pack.layout) (ex : Bool) (T : ℕ) :
    RecordsWithin y (transferData h data) ex T ↔ RecordsWithin p data ex T := by cases h; rfl

end Epoch.Round

namespace Shortening.Adaptive.Program

open BorderVNP.Crossing BorderVNP.Cover BorderVNP.Epoch BorderVNP.Epoch.Round Finset
open scoped Classical

attribute [local instance] portFintype

variable {D m k b : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I] [Fintype P] {bits : P → ℕ}
  {states : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
  {view : ∀ j, states j → PlacedPack D (Port k P j) (width bits k j) K I (depth j)}
  {e : PaidIdentity K D m} (F : Program (B := B) e view)

/-- Literal storage of the computed physical result by the stage path. -/
def Direct : Prop := ∀ i c q, view (i.val+1) (F.advance i c q) = (F.step i c).result e q

/-- Refine each physical state by its actual retained public and expanded fields. -/
abbrev Tracked (view : ∀ j, states j → PlacedPack D (Port k P j) (width bits k j) K I (depth j))
    (j : ℕ) := Σ a : states j, RecordData (view j a).pack.layout

/-- The geometric view of a record-carrying state. -/
def trackedView (view : ∀ j, states j → PlacedPack D (Port k P j) (width bits k j) K I (depth j))
    (j : ℕ) (z : Tracked view j) := view j z.1

/-- For each chosen histogram, the new records are exactly the sewn prior and payload maps. -/
noncomputable def sewData (i : Fin b) (c : Fin k → Tracked view i.val) (q : (F.step i (fun j => (c j).1)).Index e) :
    RecordData ((F.step i (fun j => (c j).1)).result e q).pack.layout where
  prior := (F.step i (fun j => (c j).1)).resultPrior e q (fun j => (c j).2.prior)
  payload := (F.step i (fun j => (c j).1)).resultPayload e q (fun j => (c j).2.payload)

set_option maxHeartbeats 2000000 in
/-- The program that executes the very same measured steps and installs their sewn records. -/
noncomputable def withRecords (direct : F.Direct) : Program (B := B) e (trackedView view) where
  step i c := F.step i (fun j => (c j).1)
  advance i c q := ⟨F.advance i (fun j => (c j).1) q,
    transferData (direct i (fun j => (c j).1) q).symm (F.sewData i c q)⟩
  tensor i c q x := F.tensor i (fun j => (c j).1) q x
  length i c q := F.length i (fun j => (c j).1) q
  concentration i c q := F.concentration i (fun j => (c j).1) q

omit [Fintype P] in
/-- The additional data have no effect on the stored physical layout or local tensor. -/
theorem withRecords_direct (direct : F.Direct) : (F.withRecords direct).Direct :=
  fun i c q => direct i (fun j => (c j).1) q

/-- The actual record fields on the executed network at each reached history. -/
noncomputable def historyRecords (direct : F.Direct) (j : ℕ) (z : ((F.withRecords direct).system.layer j).Name) :
    RecordData ((F.withRecords direct).executed j z).pack.layout :=
  transferData ((F.withRecords direct).executed_eq_state (F.withRecords_direct direct) j z).symm
    (((F.withRecords direct).system.layer j).state z).2

set_option maxHeartbeats 2000000 in
/-- Each certified physical step gives the exact induction step on the installed records.
This applies to every initial record assignment and to both counting modes. -/
theorem historyRecords_step (direct : F.Direct) (hk : 0 < k) (C : Fin b → ℕ)
    (cert : ∀ i c, (F.step i c).RecordFactor e (C i)) (ex : Bool) (i : Fin b)
    (z : ((F.withRecords direct).system.layer (i.val+1)).Name) (T : ℕ)
    (hT : ∀ j, RecordsWithin ((F.withRecords direct).executed i.val (z.1 j))
      (F.historyRecords direct i.val (z.1 j)) ex T) :
    RecordsWithin ((F.withRecords direct).executed (i.val+1) z)
      (F.historyRecords direct (i.val+1) z) ex (C i*k*T) := by
  let G := F.withRecords direct
  let c (j : Fin k) := (G.system.layer i.val).state (z.1 j)
  let q : (F.step i (fun j => (c j).1)).Index e := z.2.2
  have hchild (j : Fin k) : RecordsWithin (view i.val (c j).1) (c j).2 ex T :=
    (recordsWithin_transfer _ _ _ _).mp (hT j)
  have hpos : 0 < T := (Nat.add_pos_left (by decide : 0 < 1) _).trans_le (hchild ⟨0,hk⟩ 1)
  have cap := cert i (fun j => (c j).1) q ex (fun j => (c j).2.prior) (fun j => (c j).2.payload) (T-1)
    (fun j t => by
      have ht := hchild j t
      have he : localRecords (view i.val (c j).1).pack.layout ex (c j).2.prior (c j).2.payload
          (fun v => productAddress (depth i.val) ((view i.val (c j).1).site v) = t) ≤ T-1 := by omega
      convert! he using 1)
  rw [show 1+(T-1) = T by omega] at cap
  apply (recordsWithin_transfer _ _ _ _).mpr
  change RecordsWithin (view (i.val+1) (F.advance i (fun j => (c j).1) q))
    (transferData (direct i (fun j => (c j).1) q).symm (F.sewData i c q)) ex _
  apply (recordsWithin_transfer _ _ _ _).mpr
  intro t
  have ht := cap t
  unfold PlacedStep.resultLocalRecords at ht
  dsimp only [sewData]
  let output := (F.step i (fun j => (c j).1)).result e q
  let counts (f : Fintype (Fin k × Port k P i.val)) := 1+@localRecords D _ f _ output.pack.layout ex
    (F.sewData i c q).prior (F.sewData i c q).payload (fun v => productTileName _ (output.site v) = t)
  have same := congrArg counts (Subsingleton.elim (portFintype (k := k) (P := P) (b := i.val+1))
    (instFintypeProd (Fin k) (Port k P i.val)))
  exact same.le.trans ht

end Shortening.Adaptive.Program

end BorderVNP
end Computability
end OAI
