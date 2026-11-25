import OAI.Computability.BorderVNP.ShortenEpochRoundFlatSites

/-!
# Per-tile public and expanded record bounds on an actual epoch

The same physical histories used for the tensor and site-potential estimate
carry the actual prior and payload records at each vertex. The fixed
subdivision factor, each of the finitely many measured-step factors, and the
final bounded motion give a uniform per-tile bound through the entire tree.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch.Round

open BorderVNP.Crossing BorderVNP.Cover BorderVNP.Shortening BorderVNP.Shortening.Adaptive Finset
open scoped Classical

attribute [local instance] portFintype

/-- Retained descriptor histories and extra expanded data associated with each physical box. -/
structure RecordData {D : ℕ} {P : Type} {bits : P → ℕ} (N : Network D P bits) where
  /-- Number of earlier public descriptor records at this box. -/
  prior : N.Site → ℕ
  /-- Extra expanded data carried by this box. -/
  payload : N.Site → ℕ

/-- Reindexing the input level and the underlying pack transports a site-cap hypothesis
through the exact heterogeneous equality of the original integral route records. -/
theorem RecordData.transfer_site_cap {D d₁ d₂ : ℕ} {P I : Type} [Fintype P] [Fintype I]
    {K : Type*} {bits : P → ℕ} {L : ℝ} {p y : Pack D P bits K} {r₁ : SiteRoutes p I d₁ L}
    {r₂ : SiteRoutes y I d₂ L} (hd : d₁ = d₂) (hp : p = y) (hr : HEq r₁ r₂)
    (data : RecordData y.layout) (ex : Bool) (M : ℕ)
    (hm : ∀ t, localRecords y.layout ex data.prior data.payload (fun v => reduceMove d₂ (r₂.origin v) = t) ≤ M) :
    let stored := cast (congrArg (fun z : Pack D P bits K => RecordData z.layout) hp.symm) data
    ∀ t, localRecords p.layout ex stored.prior stored.payload (fun v => reduceMove d₁ (r₁.origin v) = t) ≤ M := by
  subst d₂; subst y
  obtain rfl := eq_of_heq hr
  exact hm

/-- The per-tile bound on one physical placed pack, including the additive unit. -/
def RecordsWithin {D d : ℕ} {P I : Type} [Fintype P] [Fintype I] {bits : P → ℕ} {R : Type*}
    (p : PlacedPack D P bits R I d) (data : RecordData p.pack.layout) (ex : Bool) (cap : ℕ) : Prop :=
  ∀ t, 1+localRecords p.pack.layout ex data.prior data.payload (fun v => productAddress d (p.site v) = t) ≤ cap

namespace InitialSites

variable {D d : ℕ} {P I : Type} [Fintype I] {R : Type*} [CommSemiring R] {bits : P → ℕ}
  {p : PlacedPack D P bits R I d} {L δ : ℝ} {hδ : 0 < δ}

/-- Subdivision retains the original vertex records and places zero extra records on each new equality box. -/
def installedData (s : InitialSites p L hδ) (data : RecordData s.pack.layout) : RecordData p.pack.layout :=
  cast (congrArg (fun z : PlacedPack D P bits R I d => RecordData z.pack.layout) s.realizes.symm)
    ⟨Sum.elim data.prior (fun _ => 0),Sum.elim data.payload (fun _ => 0)⟩

/-- Every retained input record remains controlled after the actual site subdivision. -/
theorem installedData_within [Fintype P] (s : InitialSites p L hδ) (data : RecordData s.pack.layout) (ex : Bool)
    (M : ℕ) (hM : ∀ t, localRecords s.pack.layout ex data.prior data.payload
      (fun v => reduceMove d (s.routes.origin v) = t) ≤ M) :
    RecordsWithin p (s.installedData data) ex
      ((1+3*Fintype.card (Option (allowedMoves I L) × Fin (hopCount L δ)))*(1+M)) := by
  rcases s with ⟨input,r,rfl⟩
  exact (r.initial_tensor_records (h := δ) data.prior data.payload).2 ex M hM

end InitialSites

variable {D m k b : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I] [Fintype P] {bits : P → ℕ}
  {states : ℕ → Type*} {B : Fin b → Type} [∀ i, Fintype (B i)] {depth : ℕ → ℕ}
  {view : ∀ j, states j → PlacedPack D (Port k P j) (width bits k j) K I (depth j)}
  {e : PaidIdentity K D m} (F : Program (B := B) e view)

/-- The full record-bound induction, with the actual additive input unit, uniform over every
depth and every physical profile history above the specified original tuple. -/
theorem record_tree {L δ : ℝ} {hδ : 0 < δ} (flat : Fin (k^b) → states 0)
    (sites : ∀ i, InitialSites (view 0 (flat i)) L hδ)
    (input : ∀ i, RecordData (sites i).pack.layout)
    (data : ∀ j (z : (F.system.layer j).Name), RecordData (F.executed j z).pack.layout)
    (initial : ∀ i, data 0 (flat i) = (sites i).installedData (input i))
    (ex : Bool) (M : ℕ) (hM : ∀ i t, localRecords (sites i).pack.layout ex (input i).prior (input i).payload
      (fun v => reduceMove (depth 0) ((sites i).routes.origin v) = t) ≤ M)
    (C : Fin b → ℕ)
    (step : ∀ (j : Fin b) (z : (F.system.layer (j.val+1)).Name) (T : ℕ),
      (∀ i, RecordsWithin (F.executed j.val (z.1 i)) (data j.val (z.1 i)) ex T) →
      RecordsWithin (F.executed (j.val+1) z) (data (j.val+1) z) ex (C j*T)) :
    let A := 1+∑ i, C i
    let init := (1+3*Fintype.card (Option (allowedMoves I L) × Fin (hopCount L δ)))*(1+M)
    ∀ j ≤ b, ∀ z : (F.system.layer j).Name, F.system.fromInputs (fun a => a ∈ Set.range flat) j z →
      RecordsWithin (F.executed j z) (data j z) ex (A^j*init) := by
  intro A init j
  induction j with
  | zero =>
    intro _ z hz
    obtain ⟨i,rfl⟩ := hz
    rw [initial i,pow_zero,one_mul]
    exact (sites i).installedData_within (input i) ex M (hM i)
  | succ j ih =>
    intro hj z hz t
    let i : Fin b := ⟨j,by omega⟩
    have cap := step i z (A^j*init) (fun u => ih (by omega) (z.1 u) (hz u)) t
    have hci : C i ≤ A := (single_le_sum (f := C) (fun _ _ => Nat.zero_le _) (mem_univ i)).trans (Nat.le_add_left _ _)
    exact cap.trans ((Nat.mul_le_mul_right (A^j*init) hci).trans_eq (by ring))

omit [NeZero D] [Field K] in
/-- The same physical output, flattened to ordinary row-major free ports, satisfies the
per-tile bound after the final motion. This estimate works for every public or expanded
record field carried by the terminal tree. -/
theorem flat_output_record_bound {l d : ℕ} {L A Cout : ℝ} {H T : ℕ}
    (p : PlacedPack D (Port k P b) (width bits k b) K I l)
    (out : SiteOutput p d L A Cout H) (data : RecordData p.pack.layout) (ex : Bool)
    (hT : 0 < T) (cap : RecordsWithin p data ex T) :
    ∀ t, 1+localRecords (flattenPack b p.pack).layout ex data.prior data.payload
      (fun v => reduceMove d (out.routes.flatten.origin v) = t) ≤ (1+H)*T := by
  intro t
  have hflat := SiteRoutes.flatten_records p.pack ex data.prior data.payload
    (fun v => reduceMove d (out.routes.origin v) = t)
  have hb := out.records_le ex data.prior data.payload T (fun u => (Nat.le_add_left _ _).trans (cap u)) t
  calc
    _ = 1+localRecords p.pack.layout ex data.prior data.payload
        (fun v => reduceMove d (out.routes.origin v) = t) := by
      convert! congrArg (1+·) hflat using 1
    _ ≤ (1+H)*T := (Nat.add_le_add (show 1 ≤ T from hT) hb).trans_eq (by ring)

/-- The fixed factor for the entire site-to-site tree, for either mode of counting. -/
noncomputable def epochRecordFactor (I : Type) [Fintype I] (L δ : ℝ) {b : ℕ} (C : Fin b → ℕ) (H : ℕ) :=
  (1+H)*(1+∑ i, C i)^b*(1+3*Fintype.card (Option (allowedMoves I L) × Fin (hopCount L δ)))

/-- A single factor bounds the actual intermediate records and the actual records of every
flattened terminal site pack. It is independent of the original record cap and of the
input leaf tuple. -/
theorem epoch_record_bounds {d : ℕ} {L δ A Cout : ℝ} {H : ℕ} {hδ : 0 < δ} (flat : Fin (k^b) → states 0)
    (sites : ∀ i, InitialSites (view 0 (flat i)) L hδ)
    (input : ∀ i, RecordData (sites i).pack.layout)
    (data : ∀ j (z : (F.system.layer j).Name), RecordData (F.executed j z).pack.layout)
    (initial : ∀ i, data 0 (flat i) = (sites i).installedData (input i))
    (ex : Bool) (M : ℕ) (hM : ∀ i t, localRecords (sites i).pack.layout ex (input i).prior (input i).payload
      (fun v => reduceMove (depth 0) ((sites i).routes.origin v) = t) ≤ M)
    (C : Fin b → ℕ)
    (step : ∀ (j : Fin b) (z : (F.system.layer (j.val+1)).Name) (T : ℕ),
      (∀ i, RecordsWithin (F.executed j.val (z.1 i)) (data j.val (z.1 i)) ex T) →
      RecordsWithin (F.executed (j.val+1) z) (data (j.val+1) z) ex (C j*T))
    (out : ∀ i : F.Hist flat, SiteOutput (F.terminal flat i) d L A Cout H) :
    (∀ j ≤ b, ∀ z : (F.system.layer j).Name, F.system.fromInputs (fun a => a ∈ Set.range flat) j z →
      RecordsWithin (F.executed j z) (data j z) ex (epochRecordFactor I L δ C H*(1+M))) ∧
    ∀ i : F.Hist flat,
      let z := (F.system.histories b le_rfl (leavesEquiv k (states 0) b flat)).term i
      let r := data b z
      ∀ t, 1+localRecords (flattenPack b (F.terminal flat i).pack).layout ex r.prior r.payload
        (fun v => reduceMove d ((out i).routes.flatten.origin v) = t) ≤ epochRecordFactor I L δ C H*(1+M) := by
  let S := 1+∑ i, C i
  let init := (1+3*Fintype.card (Option (allowedMoves I L) × Fin (hopCount L δ)))*(1+M)
  have hall := record_tree F flat sites input data initial ex M hM C step
  have hS : 0 < S := Nat.add_pos_left (by decide) _
  constructor
  · intro j hj z hz t
    apply (hall j hj z hz t).trans
    calc
      S^j*init ≤ S^b*init := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hS hj)
      _ ≤ (1+H)*(S^b*init) := Nat.le_mul_of_pos_left _ (by omega)
      _ = _ := by unfold epochRecordFactor; dsimp only [S,init]; ring
  · intro i z r t
    have hz := F.system.fromInputs_histories (fun a => a ∈ Set.range flat) b le_rfl
      (leavesEquiv k (states 0) b flat) (allLeaves_of_flat _ b flat (fun j => ⟨j,rfl⟩)) i
    have hb := hall b le_rfl z hz
    have hT : 0 < S^b*init := Nat.mul_pos (pow_pos hS _) (by dsimp [init]; positivity)
    exact (flat_output_record_bound (F.terminal flat i) (out i) r ex hT hb t).trans_eq
      (by unfold epochRecordFactor; dsimp only [S,init]; ring)

end Epoch.Round

end BorderVNP
end Computability
end OAI
