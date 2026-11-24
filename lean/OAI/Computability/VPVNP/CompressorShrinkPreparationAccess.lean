import OAI.Computability.VPVNP.CompressorShrinkRankAccess

/-! # Guarded source traces for the six bundle preparation visits

Every report returns the next ordinal. Reads stay within the original
level's data and the allocated arena. Writes begin at the shrinking arena.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkInput.Run

open BurstRAM PrimedStackRAM Compression SourceTransport ShrinkRankSpace
open scoped Fin.CommRing
open private collectPreimage_reject from OAI.Computability.VPVNP.CompressorSlotFrames

variable {w a g : ℕ} {X : State a (packingLaneBits a g)} {T : IncidenceDirectory w} {start : ℕ}
variable {m : Memory w} (r : Run X T start m)
local notation "Z" => plan X start
local notation "A" => Shape.A (plan X start)
local notation "B" => Shape.B (plan X start)
local notation "S" => Fintype.card X.Base * 2^(packingLaneBits a g)
local notation "sh" => placementBank X T start
local notation "p" => Shape.classifyBank (plan X start) T (placementBank X T start)
local notation "q" => Shape.collectBank (plan X start) w
local notation "K" => Shape.gatheredTable (plan X start) w T

private theorem scanned {C : Type*} {P : BurstRAM.Program w C} {fuel : ℕ}
    (step : ∀ m i rep, execute P fuel (P.start i) m [] = some rep → rep.result = some (i+1))
    (m : Memory w) (first count : ℕ) (rs : List (Report w))
    (run : runSegment P fuel (some (first : Word w)) m (List.replicate count []) = some rs) :
    StageFrame.Scanned first (first+count) rs := by
  induction count generalizing first rs m with
  | zero => change some [] = some rs at run; cases Option.some.inj run; exact .done _
  | succ n ih =>
    rw [List.replicate_succ,runSegment] at run
    cases hx : execute P fuel (P.start (first : Word w)) m [] with
    | none => rw [hx] at run; contradiction
    | some rep =>
      have inc := step m (first : Word w) rep hx
      rw [show (first : Word w)+1 = ((first+1 : ℕ) : Word w) by simp] at inc
      simp only [hx,inc,Option.map_eq_some_iff] at run
      obtain ⟨tail,rt,rfl⟩ := run
      exact .next (by omega) inc ((show first+1+n = first+(n+1) by omega) ▸ ih _ _ tail rt)

private theorem next_of {C : Type*} {P : BurstRAM.Program w C} {fuel : ℕ} {m : Memory w} {i : Word w}
    {rep : Report w} {es : List (Event w)}
    (native : execute P fuel (P.start i) m [] = some ⟨es,some (i+1)⟩)
    (actual : execute P fuel (P.start i) m [] = some rep) : rep.result = some (i+1) :=
  congrArg Report.result (Option.some.inj (actual.symm.trans native))

set_option maxHeartbeats 1500000 in
private theorem six_ordinals :
    StageFrame.Scanned 0 S r.sites ∧ StageFrame.Scanned 0 (2*B) r.clear ∧ StageFrame.Scanned 0 A r.classify ∧
      StageFrame.Scanned 0 A r.append ∧ StageFrame.Scanned 0 A r.gather ∧ StageFrame.Scanned 0 A r.rank := by
  have at_zero {C : Type} {P : BurstRAM.Program w C} {fuel n : ℕ} {mem : Memory w} {rs : List (Report w)}
      (run : runSegment P fuel (some 0) mem (List.replicate n []) = some rs)
      (step : ∀ m i rep, execute P fuel (P.start i) m [] = some rep → rep.result = some (i+1)) : StageFrame.Scanned 0 n rs := by
    simpa only [Nat.zero_add] using scanned step mem 0 n rs run
  refine ⟨at_zero r.positions (fun mem i _ ↦ next_of (ShrinkRAM.visit_native sh mem i)),
    at_zero r.ranking.clear (fun mem i _ ↦ next_of (SliceRAM.clearVisit_native (q 3) i mem)),
    at_zero r.ranking.ranked.classify (fun mem i _ ↦ next_of (BundleRAM.visit_native p mem i)),
    at_zero r.ranking.ranked.append ?_,
    at_zero r.ranking.ranked.gather (fun mem i _ ↦ next_of (BundleGather.Fixed.native (BundleGather.Fixed.parameters K) mem i)),
    at_zero r.ranking.ranked.rank.executed ?_⟩
  · intro mem i rep run
    by_cases h : i < q 0 ∧ ownerAt q mem i < q 2 ∧ mem (countAt q (ownerAt q mem i)).val < q 4
    · exact next_of (collectPreimage_native q mem i h.1 h.2.1 h.2.2) run
    · rw [collectPreimage_reject q mem i h] at run; contradiction
  · intro mem i rep run
    obtain ⟨_,hn,_,_,_⟩ := PortRankRAM.run_one (BundleGather.rankPublic q (p 10) (Fin.ofNat _ (Z).gathered) (Fin.ofNat _ (Z).ranks)) mem i (Z).Q
    exact next_of hn run

/-- Each of the first six bundle segments is ready for source transport and
has the complete sequence of native successor cursors. -/
theorem preparation_footprints (lo : ℕ) (low : ∀ c, lo ≤ (T.column c).val) (room : stop X start < 2^w) :
    let checked := fun n (rs : List (Report w)) ↦ StageFrame.Scanned 0 n rs ∧
      LogAccess (fun z ↦ lo ≤ z ∧ z < stop X start) (fun z ↦ start ≤ z ∧ z < stop X start) rs
    checked S r.sites ∧ checked (2*B) r.clear ∧ checked A r.classify ∧ checked A r.append ∧
      checked A r.gather ∧ checked A r.rank := by
  intro checked
  obtain ⟨s,c,k,l,g,rk⟩ := r.six_ordinals
  have lowStart : lo ≤ start := (low 0).trans ((Nat.le_add_right ..).trans (r.greedy.old 0))
  obtain ⟨h₁,h₂,_,h₄⟩ := range_bounds X start
  have chain : rankBase X start ≤ (Z).key ∧ (Z).key ≤ (Z).counts ∧ (Z).counts ≤ (Z).ids ∧
      (Z).ids ≤ (Z).gathered ∧ (Z).gathered ≤ (Z).ranks ∧ (Z).ranks ≤ widthBase X start := by
    refine ⟨Nat.le_add_right ..,?_,Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..⟩
    change rankBase X start+A ≤ rankBase X start+2*A; omega
  obtain ⟨hk,hc,hi,hg,hr,hw⟩ := chain
  refine ⟨⟨s,(r.placement_access lo low room).mono ?_ ?_⟩,⟨c,(r.clear_access room).mono ?_ ?_⟩,
    ⟨k,(r.classify_access lo low room).mono ?_ ?_⟩,⟨l,(r.append_access room).mono ?_ ?_⟩,
    ⟨g,(r.gather_access room).mono ?_ ?_⟩,⟨rk,(r.rank_access room).mono ?_ ?_⟩⟩
  all_goals first | exact fun _ h ↦ h.elim | (rintro z ⟨a,b⟩; exact ⟨by omega,by omega⟩)

end CompressorRecords.ShrinkInput.Run

end VPVNP
end Computability
end OAI
