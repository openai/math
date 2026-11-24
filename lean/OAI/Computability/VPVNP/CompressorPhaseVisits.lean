import OAI.Computability.VPVNP.CompressorLevelCounts
import OAI.Computability.VPVNP.CompressorRecordsDirectory
import OAI.Computability.VPVNP.RAMFinite

/-!
# Charged native directory scans on a selected compression branch

A phase may dispatch one flat scan or use short rows for each site of a
fixed kind. The two forms have different launch counts. The scope indexes
the actual base, slots, motifs or resulting sites of the selected kernel.
The directory bound charges launches, closing calls and the final controller
as well as every original data call, even for empty scans.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.PhaseVisits

open BurstRAM Compression Schedule

/-- Objects traversed by the native workers at a single level. -/
inductive Scope where
  | once | oldBase | oldSites | oldSlots | motifs | newSites | newSlots | reservedSites
  deriving DecidableEq

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {A : Type*} [CommRing A] {f : B.Entry → A} {hf : B.IsSolution f}

/-- Number of objects in the phase's scope for the selected pass, using its base, sites, slots,
or motifs as appropriate. -/
def Scope.count (sites : ℕ) (v : SelectedLevel B f hf) : Scope → ℕ
  | .once => 1
  | .oldBase => Fintype.card v.input.Base
  | .oldSites => v.input.positions
  | .oldSlots => v.oldSlots
  | .motifs => v.origin.motifCount
  | .newSites => v.outputSites
  | .newSlots => v.outputSlots
  | .reservedSites => sites

theorem Scope.count_le (s : Scope) (sites : ℕ) (v : SelectedLevel B f hf) (hv : v.input.positions ≤ sites) :
    s.count sites v ≤ sites * max 1 (slotDegree S) := by
  have hsites := Nat.le_mul_of_pos_right sites (le_max_left 1 (slotDegree S))
  have hp := hv.trans hsites
  have hold := Nat.mul_le_mul hv (v.oldDegree_le.trans (le_max_right 1 _))
  cases s with
  | once => exact v.input.positions_pos.trans_le hp
  | oldBase => exact v.baseSites_le.trans hp
  | oldSites => exact hp
  | oldSlots => exact hold
  | motifs => exact v.origin.motifCount_le.trans hold
  | newSites => exact v.outputSites_le.trans hp
  | newSlots => exact v.outputSlots_le.trans (Nat.mul_le_mul hv (le_max_right _ _))
  | reservedSites => exact hsites

/-- A fixed scan prescription. `perObject` counts data calls at each
physical object or the full work of its short rows. -/
structure Phase where
  /-- Set of objects over which this native phase is scheduled. -/
  scope : Scope
  /-- Bound on worker visits charged to each object in the phase's scope. -/
  perObject : ℕ

/-- Per-object charge including the worker visit budget and two calls for entering and closing
a row. -/
def Phase.weight (p : Phase) := p.perObject + 2

/-- Native pass families of the fixed finite block. -/
structure Plan (S : BlockSchedule k) where
  /-- List of native phases assigned to each shrinking substep of a block. -/
  shrink : Fin S.steps → List Phase
  /-- List of native phases assigned to the degree refresh at the end of a block. -/
  refresh : List Phase

/-- Recover the phase list appropriate to the origin of the actual state pass. -/
def Plan.phases {a g b n : ℕ} {X : State a g} {p : StatePass A X b n}
    (P : Plan S) : PassOrigin B f hf p → List Phase
  | .shrink i .. => P.shrink i
  | .refresh .. => P.refresh

/-- Largest total phase weight among the refresh and all indexed shrinking passes. -/
noncomputable def Plan.levelRate (P : Plan S) :=
  max ((P.refresh.map Phase.weight).sum) (Finset.univ.sup fun i ↦ ((P.shrink i).map Phase.weight).sum)

theorem Plan.phases_rate (P : Plan S) {a g b n : ℕ} {X : State a g} {p : StatePass A X b n}
    (o : PassOrigin B f hf p) : ((P.phases o).map Phase.weight).sum ≤ P.levelRate := by
  cases o with
  | shrink i _ _ => exact (Finset.le_sup (f := fun j : Fin S.steps ↦ ((P.shrink j).map Phase.weight).sum)
      (Finset.mem_univ i)).trans (le_max_right _ _)
  | refresh => exact le_max_left _ _

variable {d w : ℕ}

/-- Number of charged calls in a row list, adding launch and close to each row's data-report
count. -/
def calls (rows : List (Directory.Row d w)) : ℕ :=
  (rows.map fun r ↦ r.reports.length+2).sum

private theorem calls_append (rs ss : List (Directory.Row d w)) :
    calls (rs++ss) = calls rs + calls ss := by simp [calls]

/-- Either a whole-phase cursor scan, or an ordered family of short row
groups. In the second form each group pays its own launches and closes. -/
inductive Rows (d w jobs visits : ℕ) where
  | flat (row : Directory.Row d w) (length : row.reports.length ≤ jobs*visits)
  | indexed (atObject : Fin jobs → List (Directory.Row d w))
      (length : ∀ i, calls (atObject i) ≤ visits)

/-- Chronological directory rows of a phase, either one flat scan or the concatenation of its
per-object rows. -/
def Rows.log {jobs visits : ℕ} : Rows d w jobs visits → List (Directory.Row d w)
  | .flat row _ => [row]
  | .indexed rows _ => (List.finRange jobs).flatMap rows

private theorem flat_calls {ι : Type*} (g : ι → List (Directory.Row d w)) (is : List ι) (C : ℕ)
    (hg : ∀ i ∈ is, calls (g i) ≤ C) : calls (is.flatMap g) ≤ is.length*C := by
  induction is with
  | nil => simp [calls]
  | cons i is ih =>
    rw [List.flatMap_cons,calls_append,List.length_cons,Nat.succ_mul]
    rw [Nat.add_comm (is.length*C) C]
    exact Nat.add_le_add (hg i (by simp)) (ih fun j hj ↦ hg _ (by simp [hj]))

theorem Rows.calls_le {jobs visits cap : ℕ} (r : Rows d w jobs visits) (h : jobs ≤ cap) (hc : 1 ≤ cap) :
    calls r.log ≤ cap*(visits+2) := by
  cases r with
  | flat row hlen =>
    have h' := hlen.trans (Nat.mul_le_mul_right visits h)
    have htwo : 2 ≤ cap*2 := by omega
    simp only [Rows.log,calls,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_add]
    omega
  | indexed rows hr =>
    exact (flat_calls rows _ visits (fun i _ ↦ hr i)).trans (by
      simp only [List.length_finRange]; exact Nat.mul_le_mul h (by omega))

/-- Each occurrence has its own physical memory and worker. The two
ordinals distinguish equal phase sizes and repeated equal input states. -/
abbrev LevelRows (sites : ℕ) (v : SelectedLevel B f hf) :=
  (levelOrdinal phaseOrdinal : ℕ) → (p : Phase) → Rows d w (p.scope.count sites v) p.perObject

private def phaseLog {sites : ℕ} {v : SelectedLevel B f hf} (rows : LevelRows (d := d) (w := w) sites v)
    (level : ℕ) : ℕ → List Phase → List (Directory.Row d w)
  | _, [] => []
  | i, p::ps => (rows level i p).log ++ phaseLog rows level (i+1) ps

/-- Directory log for the phases of one selected level, numbered from phase zero at that level. -/
def levelLog (P : Plan S) (sites : ℕ) (v : SelectedLevel B f hf) (rows : LevelRows (d := d) (w := w) sites v)
    (level : ℕ := 0) := phaseLog rows level 0 (P.phases v.origin)

private theorem phaseSum (sites : ℕ) (v : SelectedLevel B f hf) (rows : LevelRows (d := d) (w := w) sites v)
    (hv : v.input.positions ≤ sites) (ps : List Phase) (level i : ℕ) :
    calls (phaseLog rows level i ps) ≤ (sites*max 1 (slotDegree S))*(ps.map Phase.weight).sum := by
  have hc := Nat.mul_pos (v.input.positions_pos.trans_le hv) (le_max_left 1 (slotDegree S))
  induction ps generalizing i with
  | nil => simp [phaseLog,calls]
  | cons p ps ih =>
    rw [phaseLog,calls_append,List.map_cons,List.sum_cons,Nat.mul_add]
    exact Nat.add_le_add ((rows level i p).calls_le (p.scope.count_le sites v hv) hc) (ih _)

theorem levelLog_calls (P : Plan S) (sites : ℕ) (v : SelectedLevel B f hf) (rows : LevelRows (d := d) (w := w) sites v)
    (hv : v.input.positions ≤ sites) (level : ℕ := 0) :
    calls (levelLog P sites v rows level) ≤ sites * max 1 (slotDegree S) * P.levelRate :=
  (phaseSum sites v rows hv _ _ _).trans (Nat.mul_le_mul_left _ (P.phases_rate v.origin))

/-- Concatenate the directory logs of successive selected levels while advancing the level
index. -/
def levelLogs (P : Plan S) (sites : ℕ)
    (groups : ∀ v : SelectedLevel B f hf, LevelRows (d := d) (w := w) sites v) :
    ℕ → List (SelectedLevel B f hf) → List (Directory.Row d w)
  | _, [] => []
  | i, v::vs => levelLog P sites v (groups v) i ++ levelLogs P sites groups (i+1) vs

/-- Chronological rows on the selected branch, including the level-zero
cursor initialization in `initial`. -/
def branchRows (P : Plan S) (sites : ℕ) (levels : List (SelectedLevel B f hf))
    (initial : List (Directory.Row d w)) (groups : ∀ v : SelectedLevel B f hf, LevelRows (d := d) (w := w) sites v) :=
  initial ++ levelLogs P sites groups 0 levels

private theorem levelLogs_calls (P : Plan S) (sites : ℕ) (levels : List (SelectedLevel B f hf))
    (groups : ∀ v : SelectedLevel B f hf, LevelRows (d := d) (w := w) sites v)
    (hs : ∀ v ∈ levels, v.input.positions ≤ sites) (i : ℕ) :
    calls (levelLogs P sites groups i levels) ≤ levels.length*(sites*max 1 (slotDegree S)*P.levelRate) := by
  induction levels generalizing i with
  | nil => simp [calls,levelLogs]
  | cons v vs ih =>
    rw [levelLogs,calls_append,List.length_cons,Nat.succ_mul,Nat.add_comm (vs.length*_) _]
    exact Nat.add_le_add (levelLog_calls P sites v _ (hs v List.mem_cons_self) i)
      (ih (fun j hj ↦ hs j (List.mem_cons_of_mem _ hj)) _)

theorem branchRows_calls (P : Plan S) {T n : ℕ} (h : T*S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
    (z : (B.execute f hf T h X).Choices) (initial : List (Directory.Row d w))
    (groups : ∀ v : SelectedLevel B f hf, LevelRows (d := d) (w := w) X.positions v) :
    calls (branchRows P X.positions (executeLevels B f hf T h X z) initial groups) ≤
      calls initial + (S.steps+1)*T*(X.positions*max 1 (slotDegree S)*P.levelRate) := by
  rw [branchRows,calls_append]
  apply Nat.add_le_add_left
  exact (levelLogs_calls _ _ _ _ (fun v hv ↦ (executeLevels_limits B f hf T h X z v hv).1) _).trans
    (Nat.mul_le_mul_right _ (executeLevels_length B f hf T h X z))

private theorem count_le_events (es : List (Event w)) : countProbes es ≤ es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e <;> simp only [countProbes,List.length_cons] <;> omega

private theorem cost_cap (rs : List (Report w)) (cap : ℕ) (h : ∀ r ∈ rs, r.events.length < cap) :
    RAMBuckets.cost Report.probes rs ≤ rs.length*cap := by
  induction rs with
  | nil => simp [RAMBuckets.cost]
  | cons r rs ih =>
    change 1+r.probes+_ ≤ (rs.length+1)*cap
    rw [Nat.succ_mul,Nat.add_comm (rs.length*cap) cap]
    apply Nat.add_le_add _ (ih fun s hs ↦ h _ (by simp [hs]))
    have hp := (count_le_events r.events).trans_lt (h r (by simp))
    change 1+countProbes r.events ≤ cap
    omega

private theorem linked_length (C : Catalog d) (i : Fin d) (ports : Ports w) (m : Memory w) (rs : List (Report w)) :
    (linkedRows C i ports m rs).length = rs.length := by
  induction rs generalizing m with
  | nil => rfl
  | cons r rs ih => exact congrArg Nat.succ (ih _)

theorem directory_length (C : Catalog d) (ports : Ports w) (m : Memory w) (rows : List (Directory.Row d w)) :
    (rows.flatMap (Directory.Row.log C ports) ++ [Directory.terminalReport (d := d) ports
      (Directory.finalMemory C ports m rows)]).length = calls rows+1 := by
  simp only [List.length_append,List.length_cons,List.length_nil]
  congr 1
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    rw [List.flatMap_cons,List.length_append,ih]
    simp only [Directory.Row.log,List.length_cons,List.length_append,linked_length,List.length_nil,
      calls,List.map_cons,List.sum_cons]

/-- Run the linked table on a physically valid directory and charge all
returned reports, including launch, stop and terminal controller. -/
theorem directory_run (C : Catalog d) (ports : Ports w) (m : Memory w) (rows : List (Directory.Row d w)) (cap : ℕ)
    (fit : d+1 ≤ 2^w) (hcap : 6+2*(d+1)+5 ≤ cap) (valid : Directory.Valid C ports cap m rows) :
    ∃ reports, runSegment (Directory.program C ports) cap (some 0) m
      (rows.flatMap Directory.Row.choicesWithControl ++ [[]]) = some reports ∧
      (∀ r ∈ reports, r.events.length < cap ∧ r.probes < cap) ∧
      RAMBuckets.cost Report.probes reports ≤ (calls rows+1)*cap := by
  let rs := rows.flatMap (Directory.Row.log C ports) ++ [Directory.terminalReport (d := d) ports
    (Directory.finalMemory C ports m rows)]
  have hr := Directory.run C ports rows m cap fit hcap valid
  have steps := localSegment_event_bound ((runSegment_iff ..).mp hr).1
  exact ⟨rs,hr,fun r h ↦ ⟨steps r h,(count_le_events r.events).trans_lt (steps r h)⟩,
    (cost_cap rs cap steps).trans_eq (congrArg (· * cap) (directory_length C ports m rows))⟩

end CompressorRecords.PhaseVisits

end

end VPVNP
end Computability
end OAI
