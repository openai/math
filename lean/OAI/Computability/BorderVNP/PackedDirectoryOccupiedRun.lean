import OAI.Computability.BorderVNP.PackedDirectoryOccupiedRoom

/-! # Native publication using the occupied private and live placement words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.ISA

open RoutingISA VPVNP.BurstRAM
open private limitedSizes from OAI.Computability.BorderVNP.PackedDirectoryOccupiedRoom

/-- Publish the compact seven-word directory starting from the actual native frame and
occupied placements. Word fit is needed only for meaningful entries. The unused terminal
live slices can read any word at all. -/
theorem occupied_program_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (d : Layout) (base pb lb extent : ℕ) (bound : d.DestinationBounds)
    (teams : 0 < d.teams) (fields : 0 < d.fields) (sites : d.processors ≤ d.sites)
    (originals : d.entries ≤ d.teams*d.sites)
    (shape : frameLayout (readings pub) (readings m) = d)
    (starts : frameField (readings pub) (readings m) 8 = base ∧
      frameField (readings pub) (readings m) 64 = pb ∧ frameField (readings pub) (readings m) 65 = lb)
    (privateRoom : ∀ j < d.entries, (placement (readings m) pb j).2 ≤ extent)
    (liveRoom : ∀ a < d.teams*d.sites, (placement (readings m) lb a).2 ≤ extent)
    (room : wordBound (placementBound d pb lb extent) < 2^w)
    (before : (pub 0).val+70 < base) (arrays : base+7*d.candidates ≤ pb ∧ base+7*d.candidates ≤ lb) :
    let pp := placement (readings m) pb
    let lp := placement (readings m) lb
    let rows := d.directory pp lp
    ∃ es t, Runs pub mac program s m es t (publish m (pub 0).val base rows) ∧
      traceCost es ≤ setup.slots+(candidate.slots+19)*(8*(d.teams*d.sites))+8 := by
  intro pp lp rows
  let B := placementBound d pb lb extent
  have ss := limitedSizes d pb lb extent pp lp privateRoom liveRoom
  have scale : B ≤ wordBound B := by unfold wordBound; nlinarith [Nat.zero_le (B^4),Nat.zero_le (B^3),Nat.zero_le (B^2)]
  have fits := occupied_candidates_fit pp lp bound fields privateRoom liveRoom
    (fun a => (m (lb+a*2+1)).isLt) room
  have begin := program_runs pub mac s m
  dsimp only at begin
  rw [shape,starts.1,starts.2.1,starts.2.2] at begin
  have slots : d.processors*d.literal ≤ d.sites*d.block :=
    (Nat.mul_le_mul_left _ (by
      change d.literal ≤ d.fields*d.literal+(d.teams-1)*d.link
      exact (Nat.le_mul_of_pos_left _ fields).trans (Nat.le_add_right ..))).trans bound.room
  obtain ⟨es,t,run,ticks⟩ := begin teams bound.processors bound.block before (ss.stride.trans_lt (scale.trans_lt room))
    (arrays.1.trans_lt (ss.bases.1.trans_lt (scale.trans_lt room))) arrays.1 arrays.2 fits
  have nc := d.candidates_le bound.block bound.fields slots sites originals
  exact ⟨es,t,run,ticks.trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ nc) _) _)⟩

end Packing.Directory.ISA

end BorderVNP
end Computability
end OAI
