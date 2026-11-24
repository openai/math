import OAI.Computability.VPVNP.CompressorPhaseVisits
import OAI.Computability.VPVNP.CompressorRecordsOnline
import OAI.Computability.VPVNP.CompressorRecordsDirectoryCursor
import OAI.Computability.VPVNP.CursorBranchCommunication

/-!
# Uniform cost of the selected branch's linked descriptor scans

The native calendar makes three calls before each scan and one closing
call. The scan consumes the source worker's complete tape. The theorem
charges these four calls even when that tape is empty. The constant is
chosen from the initial rows, the finite block's multiplicities, and the
native instruction cap, before any input length or term choice.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PhaseVisits

open BurstRAM Compression Schedule CursorNetwork CursorBounds Filter
open private count_le_events cost_cap from OAI.Computability.VPVNP.CompressorPhaseVisits

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}
variable {d w : ℕ}

private theorem source_length {C : Catalog d} {ports : Ports w} {row : Directory.Row d w}
    (h : row.Valid C ports) : row.choices.length = row.reports.length := by
  have hv := ((runSegment_iff ..).mp h.sourceRun).2.2
  simpa [branchPaths] using (congrArg List.length hv).symm

private theorem online_tape_length (C : Catalog d) (ports : Ports w) (rows : List (Directory.Row d w))
    (h : ∀ r ∈ rows, r.Valid C ports) :
    (rows.flatMap Online.rowChoices ++ [[]]).length ≤ 2*calls rows+1 := by
  have bound : (rows.flatMap Online.rowChoices).length ≤ 2*calls rows := by
    induction rows with
    | nil => simp [calls]
    | cons r rs ih =>
      have hl := source_length (h r (by simp))
      have ht := ih (fun r hr ↦ h _ (by simp [hr]))
      rw [List.flatMap_cons,List.length_append]
      change (Online.rowChoices r).length+_ ≤ 2*((r.reports.length+2)+calls rs)
      simp only [Online.rowChoices,List.length_cons,List.length_append,List.length_nil,hl]
      omega
  simpa only [List.length_append,List.length_cons,List.length_nil] using Nat.add_le_add_right bound 1

/-- Source-data calls and both control calls in the initial cursor directory. -/
theorem cursorRow_calls (m : Memory w) (base lanes a width columns : ℕ) :
    calls [Directory.Cursor.row m base lanes a width columns] = CursorRAM.rowCount base lanes a + 2 := by
  simp [calls,Directory.Cursor.row,CursorRAM.scanReports_length]

private theorem blocks_le_log (B : S.Templates) (u : PairExponents B.growthConstant) {n : ℕ} (hn : 1 ≤ n) :
    blockCount (u.θ : ℝ) n ≤ n.log2+1 := by
  have hθ : (u.θ : ℝ) ≤ 1 := by
    have := (Rat.cast_lt (K := ℝ)).mpr u.theta_lt
    norm_num at this; linarith
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  apply le_trans _ (BurstRAM.clog_le_log2_succ n)
  rw [blockCount,← Real.natCeil_logb_natCast 2 n]
  exact (Nat.floor_le_floor (mul_le_of_le_one_left (Real.logb_nonneg (by norm_num) hn₁) hθ)).trans
    (Nat.floor_le_ceil _)

/-- Charged accesses for the online controller and worker reports of one
whole selected branch. The successful run and individual source runs are
the native caller's semantic obligations. There is no traffic hypothesis on
their combined reports. -/
theorem online_run_budget (B : S.Templates) (u : PairExponents B.growthConstant) (P : Plan S)
    (H I q b n : ℕ) (hn : 1 ≤ n) {base lanes : ℕ}
    (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
    (hT : blockCount (u.θ : ℝ) n*S.laneBits ≤ lanes)
    {A : Type*} [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f)
    (z : (B.execute f hf _ hT (pairInput S labels hD)).Choices)
    (C : Catalog d) (ports : Ports w) (initial : List (Directory.Row d w))
    (groups : ∀ v : SelectedLevel B f hf, LevelRows (d := d) (w := w) (pairInput S labels hD).positions v)
    (hinit : calls initial ≤ I*(pairInput S labels hD).positions) :
    let X := pairInput S labels hD
    let T := blockCount (u.θ : ℝ) n
    let rows := branchRows P X.positions (executeLevels B f hf T hT X z) initial groups
    let K := (2*(I + (S.steps+1)*max 1 (slotDegree S)*P.levelRate)+1)*H
    ∀ {V : Type*} (M : BurstRAM.Program w V) (s : Word w) (mem : Memory w) (cap : ℕ)
      (rs : List (Report w)),
      (∀ r ∈ rows, r.Valid C ports) → cap ≤ H*(n.log2+1)^q →
      runSegment M cap (some s) mem (rows.flatMap Online.rowChoices ++ [[]]) = some rs →
      (∀ r ∈ rs, r.events.length < cap ∧ r.probes < cap) ∧
      RAMBuckets.cost Report.probes rs ≤ K * initialPositions b n * (n.log2+1)^(q+1) := by
  intro X T rows K V M s mem cap rs hrows hcap hr
  let L := n.log2+1
  have ht := blocks_le_log B u hn
  change T ≤ L at ht
  have hc := branchRows_calls P hT X z initial groups
  let F := I + (S.steps+1)*max 1 (slotDegree S)*P.levelRate
  have hcharged : calls rows ≤ F*X.positions*L := by
    apply hc.trans
    calc
      _ ≤ I*X.positions*L + (S.steps+1)*L*(X.positions*max 1 (slotDegree S)*P.levelRate) :=
        Nat.add_le_add (hinit.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ht))
      _ = _ := by dsimp only [F]; ring
  have hnum := online_tape_length C ports rows hrows
  have he := congrArg List.length ((runSegment_iff ..).mp hr).2.2
  have hlen : rs.length ≤ 2*calls rows+1 := (by simpa [branchPaths] using he : rs.length = _).le.trans hnum
  have hP : 1 ≤ X.positions*L := Nat.mul_pos X.positions_pos (Nat.succ_pos _)
  have hcalls : rs.length ≤ (2*F+1)*X.positions*L := hlen.trans (by
    have hh := Nat.add_le_add (Nat.mul_le_mul_left 2 hcharged) hP
    exact hh.trans_eq (by ring))
  have hstep := localSegment_event_bound ((runSegment_iff ..).mp hr).1
  refine ⟨fun r h ↦ ⟨hstep r h,(count_le_events r.events).trans_lt (hstep r h)⟩,
    (cost_cap rs cap hstep).trans ((Nat.mul_le_mul hcalls hcap).trans_eq ?_)⟩
  have hx := pairInput_positions S labels hD
  change X.positions = initialPositions b n at hx
  rw [hx]
  dsimp only [F,K,L]; ring

end CompressorRecords.PhaseVisits

end VPVNP
end Computability
end OAI
