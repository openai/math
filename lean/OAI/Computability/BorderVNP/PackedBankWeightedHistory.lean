import OAI.Computability.BorderVNP.PackedBankProgramCapacity
import OAI.Computability.BorderVNP.PackedHistoryOuterPrivateSites
import OAI.Computability.BorderVNP.PackedSiteRecords

/-! # Transporting a site's storage cost through an enriched outer history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Epoch.Round

/-- The chosen storage cost and the separate expanded work at each physical site. -/
def Site.Programs.weightedFields {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
    (pr : Site.Programs N) (weight : Site → ℕ) : RecordData N :=
  ⟨fun v => weight (pr v).program,fun v => (pr v).program.expandedLoad⟩

end Packing.Inherited

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Packing Packing.Inherited PhysicalEpochs
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2300000
set_option maxRecDepth 3000

universe u

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ} {e : PaidIdentity K D m}
    {S : SiteSchedule e} {start T : ℕ} {shape : ℕ → PublicCapacity.Shape} {W : ℕ → Type} [∀ t, Fintype (W t)]
    {good : ∀ t, State S start P bits shape W t → Prop} {deep : S.floor+1+S.drop*T ≤ start}
    {V : ℕ → ℕ → Type} [∀ t i, Fintype (V t i)] {w : ℕ → ℕ → ℕ}
    (M : Machine.{0,u} deep good V w) (rows : ∀ n hn, (M n hn).F.SiteRows) (number : e.Entry → ℕ)
    (weight : Site → ℕ) (F : ℕ) (ex : Bool)

local notation3 "Fields" => fun {Q : Type} [Fintype Q] {bw : Q → ℕ} {N : Network D Q bw} (pr : Site.Programs N) =>
  pr.weightedFields weight

/-- A capacity certificate on the exact installed program of one outer epoch. -/
abbrev StepCapacity : Prop := ∀ n hn (c : Fin (fan S) → Admissible good n) (old : ∀ j, Site.Programs (c j).val.pack.layout) B,
  (∀ j, SiteCap (c j).val.route (Fields (old j)) ex B) → ∀ q,
  SiteCap ((M n hn).term c q).val.route (Fields ((M n hn).privatePrograms (rows n hn) c old number q)) ex (F*B)

private theorem step_capacity (cert : M.StepCapacity rows number weight F ex) {n : ℕ} (hn : n<T)
    (c : Fin (fan S) → Admissible good n) (old : ∀ j, Site.Programs (c j).val.pack.layout) (B : ℕ)
    (hchild : ∀ j, SiteCap (c j).val.route (Fields (old j)) ex B) (q : (M.epoch n c).Index) :
    SiteCap ((M.epoch n c).term q).val.route (Fields (M.stepPrivatePrograms rows number hn c old q)) ex (F*B) := by
  let family (z : ProfileSum (Admissible good (n+1))) := (j : z.Index) → Site.Programs (z.term j).val.pack.layout
  have carry {z y : ProfileSum (Admissible good (n+1))} (he : z = y) (f : family y)
      (h : ∀ j : y.Index, SiteCap (y.term j).val.route (Fields (f j)) ex (F*B)) :
      ∀ j : z.Index, SiteCap (z.term j).val.route (Fields ((Eq.mpr (congrArg family he) f) j)) ex (F*B) := by
    subst y
    exact h
  have he : M.epoch n c = (M n hn).choice c := dite_eq_left hn
  exact carry he ((M n hn).privatePrograms (rows n hn) c old number) (cert n hn c old B hchild) q

variable (bottom : Admissible good 0) (base : Site.Programs bottom.val.pack.layout)

/-- The routed tile cap follows the same outer histogram ordinals as the actual
site programs, with one factor per completed epoch. -/
theorem historyPrivatePrograms_weightedCap (cert : M.StepCapacity rows number weight F ex) (B : ℕ)
    (hbase : SiteCap bottom.val.route (Fields base) ex B) (n : ℕ) (hn : n≤T) (q : (packHistory bottom M.epoch n).Index) :
    SiteCap ((packHistory bottom M.epoch n).term q).val.route
      (Fields (M.historyPrivatePrograms rows number bottom base n hn q)) ex (F^n*B) := by
  induction n with
  | zero => rw [pow_zero,one_mul]; exact hbase
  | succ n ih =>
    let child := fun j => (packHistory bottom M.epoch n).term (q.1 j)
    let pr := fun j => M.historyPrivatePrograms rows number bottom base n (Nat.le_of_succ_le hn) (q.1 j)
    rw [pow_succ',Nat.mul_assoc]
    exact M.step_capacity rows number weight F ex cert (Nat.lt_of_succ_le hn) child pr (F^n*B)
      (fun j => ih (Nat.le_of_succ_le hn) (q.1 j)) q.2

/-- Flattening the terminal ports preserves the storage cost on the exact returned site programs. -/
theorem terminalPrivatePrograms_weightedCap (cert : M.StepCapacity rows number weight F ex) (B : ℕ)
    (hbase : SiteCap bottom.val.route (Fields base) ex B) (q : (packHistory bottom M.epoch T).Index) :
    let state := ((packHistory bottom M.epoch T).term q).val
    let pr := M.terminalPrivatePrograms rows number bottom base q
    SiteCap state.route.flatten (Fields pr) ex (F^T*B) := by
  intro state pr tile
  let fields := Fields (M.historyPrivatePrograms rows number bottom base T le_rfl q)
  have flat := SiteRoutes.flatten_records (k := fan S) (b := T) state.pack ex fields.prior fields.payload
    (fun v => reduceMove (depth S start T) (state.route.origin v) = tile)
  exact (congrArg (1+·) flat).le.trans (M.historyPrivatePrograms_weightedCap rows number weight F ex bottom base cert B hbase T le_rfl q tile)

end PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

end BorderVNP
end Computability
end OAI
