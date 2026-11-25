import OAI.Computability.BorderVNP.DiagonalEnrichedLeafPayload
import OAI.Computability.BorderVNP.DiagonalDenseStagePayload

/-! # Scalar occurrence budgets through actual enriched dense program histories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries.EnrichedSiteReplay

open Crossing Shortening Cover Epoch Epoch.Round Adaptive Packing PackedHistoryCircuit.Normalized
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u

variable {D m d exp : ℕ} [NeZero D] {K E P Team Param Gadget : Type} [Field K] [Field E]
  [Fintype P] [Fintype Team] [Fintype Param] {bits : P → ℕ} {e : PaidIdentity K D m}
  {S : PackedHistoryCircuit.Normalized.SiteSchedule e} {A : ℕ → Type u}
  {view : S.GeometricView d P bits A} {F : S.EnrichedProgram d view}

omit [NeZero D] [Field K] in
private theorem save_payload {Q I : Type} [Fintype I] {n cap : ℕ} {widths : Q → ℕ}
    (p z : PlacedPack D Q widths K I n) (number : p.pack.layout.Edge ↪ Fin cap)
    (eq : z = p.dense number) (t : Tracked Team Param Gadget exp p.pack.layout)
    (r : RecordData p.pack.layout) (bound : PayloadBound t.tags r.payload) :
    let save : Storage p.pack.layout z.pack.layout := by rw [eq]; exact Storage.dense _ number
    PayloadBound (save.tracked t).tags
      (transferData eq.symm (⟨r.prior,r.payload⟩ : RecordData (p.dense number).pack.layout)).payload := by
  subst z
  exact bound.stored (Storage.dense _ number)

variable (save : F.SaveNames) (y : e.Entry → E)
  (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
    MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget)

omit [Fintype P] in
/-- Record fields and tagged entries are saved using the same physical dense
cable numbering and the same attained profile. -/
theorem move_payloadBound {j : ℕ} (hj : j < S.rounds) (c : Fin S.fanIn → A j)
    (tags : ∀ i, Tracked Team Param Gadget exp (view j (c i)).pack.layout)
    (r : ∀ i, RecordData (view j (c i)).pack.layout) (q : (F.stage ⟨j,hj⟩ c).Index e)
    (old : ∀ i, PayloadBound (tags i).tags (r i).payload) :
    PayloadBound (((storage save) ⟨j,hj⟩ c q).tracked
      (DenseReplay.stageOutput (F.stage ⟨j,hj⟩ c) tags e y hy pos q)).tags (F.saveData save ⟨j,hj⟩ c q r).payload := by
  let i : Fin S.rounds := ⟨j,hj⟩
  let s := F.stage i c
  let raw : RecordData (s.result e q).pack.layout :=
    ⟨s.resultPrior e q (fun h => (r h).prior),s.resultPayload e q (fun h => (r h).payload)⟩
  have stage := DenseReplay.stageOutput_payloadBound s tags e y hy pos q (fun h => (r h).payload) old
  exact save_payload (s.result e q) (view (j+1) (F.advance i c q)) (save.number i c q)
    (save.stored i c q) (DenseReplay.stageOutput s tags e y hy pos q) raw stage

/-- Enumerate the original team positions as in the nested tagged replay. -/
noncomputable local instance {n : ℕ} : Fintype (Port S.fanIn Team n) := Replay.batchFinite S.fanIn Team n

omit [Fintype P] in
/-- Through the complete nested tree, the conditioned specialized tags on every
actual stored history obey the very `F.replayRecords` payload at that history. -/
theorem replay_payloadBound (n : ℕ) (hn : n ≤ S.rounds) (flat : Fin (S.fanIn^n) → A 0)
    (tags : ∀ i, Tracked Team Param Gadget exp (view 0 (flat i)).pack.layout)
    (r : ∀ i, RecordData (view 0 (flat i)).pack.layout)
    (old : ∀ i, PayloadBound (tags i).tags (r i).payload) (q : F.FlatHist n hn flat) :
    PayloadBound (Replay.publicReplay F.system (fun j a => (view j a).pack.layout)
      (DenseReplay.move F y hy pos (storage save)) n hn _ (Replay.flatInputs _ n flat tags) q).tags
      (F.replayRecords save n hn flat r q).payload := by
  induction n with
  | zero => exact old 0
  | succ n ih =>
    let hj := Nat.lt_of_succ_le hn
    let sub (j : Fin S.fanIn) (x : Fin (S.fanIn^n)) := flat (copyIndex S.fanIn n (j,x))
    let c (j : Fin S.fanIn) := (F.system.layer n).state
      ((F.system.histories n hj.le (leavesEquiv S.fanIn _ n (sub j))).term (q.1 j))
    let tr (j : Fin S.fanIn) := Replay.publicReplay F.system (fun l a => (view l a).pack.layout)
      (DenseReplay.move F y hy pos (storage save)) n hj.le _
      (Replay.flatInputs _ n (sub j) (fun x => tags (copyIndex S.fanIn n (j,x)))) (q.1 j)
    let recs (j : Fin S.fanIn) := F.replayRecords save n hj.le (sub j) (fun x => r (copyIndex S.fanIn n (j,x))) (q.1 j)
    have bounds (j) : PayloadBound (tr j).tags (recs j).payload :=
      ih hj.le (sub j) (fun x => tags (copyIndex S.fanIn n (j,x))) (fun x => r (copyIndex S.fanIn n (j,x)))
        (fun x => old _) (q.1 j)
    exact move_payloadBound (F := F) save y hy pos hj c tr recs q.2 bounds

variable {input : Fin (S.fanIn^S.rounds) → Pack D P bits K}
  {route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget}
  (run : PackedHistoryCircuit.Normalized.SiteSchedule.EnrichedExecution F input route)

/-- Flattening the external port labels does not alter the scalar counts at an
internal site. The attained specialized site term is charged to its own stored
record map from the enriched program. -/
theorem term_payloadBound (t : ∀ i, Tracked Team Param Gadget exp (input i).layout)
    (r : ∀ i, RecordData (input i).layout) (old : ∀ i, PayloadBound (t i).tags (r i).payload)
    (q : F.Hist run.flat) :
    PayloadBound (term run save y hy pos t q).tags (run.recordFields r save q).payload := by
  have result := replay_payloadBound save y hy pos S.rounds le_rfl run.flat (fun i => installed run i (t i))
    (fun i => (run.initialSites i).installedData (run.inputFields r i)) (fun i => installed_payloadBound run r i (t i) (old i)) q
  exact fun v z x g => result v z _ g

end Diagonal.CellEntries.EnrichedSiteReplay

end BorderVNP
end Computability
end OAI
