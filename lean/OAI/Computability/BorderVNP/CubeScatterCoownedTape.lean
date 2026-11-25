import OAI.Computability.BorderVNP.CubeScatterTransmissionLocalTape

/-! # The local transmission tape determined by the four public descriptor fields -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open private sharedHere_fields from OAI.Computability.BorderVNP.CubeScatterTransmissionLocalTape

/-- List the assigned bits of each shared row whose two endpoints are the current team,
in native row order and then in increasing offset order. -/
def coownedStream {N : ℕ} (tab : TableLayout) (row : ℕ → TableRow) (u : Fin N)
    (bits : ℕ → ℕ → Bool) : List Bool :=
  (List.range tab.count).flatMap fun i =>
    if (row i).kind=0 ∧ (row i).first=u.val ∧ (row i).second=u.val then
      List.ofFn (fun j : Fin (row i).width => bits i j.val)
    else []

private theorem sharedHere_iff {w : ℕ} (r : Range w) (self : Word w) :
    r.selected self = some (some .sharedHere) ↔ r.kind = 0 ∧ self = r.teamA ∧ r.teamA = r.teamB := by
  refine ⟨sharedHere_fields,?_⟩
  rintro ⟨tag,localTeam,same⟩
  simp [Range.selected,Range.bank,decision,Decision.role,tag,localTeam,same]

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}

/-- In any returned delivery, the complete local word for an assignment agrees with the
layout-defined stream. It depends only on the public record columns and the assigned bits. -/
theorem ReturnedDelivery.tableChoiceBits_eq_coownedStream
    (f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins)
    (u : Fin (R+1)) (bits : ℕ → ℕ → Bool) :
    tableChoiceBits (H u).rows (H u).team bits (H u).count = coownedStream f.table f.row u bits := by
  let take (i : ℕ) := if (f.row i).kind=0 ∧ (f.row i).first=u.val ∧ (f.row i).second=u.val then
      List.ofFn (fun j : Fin (f.row i).width => bits i j.val) else []
  have atRow (i : ℕ) (hi : i < f.table.count) : ((H u).rows i).choiceBits (H u).team (bits i) = take i := by
    obtain ⟨tag,first,second,len,_⟩ := tableRange_fields (f.image u) f.allocated (f.records u) hi
    rw [← f.ranges u] at tag first second len
    have here := (f.bank u).team
    have sel : ((H u).rows i).selected (H u).team = some (some .sharedHere) ↔
        (f.row i).kind = 0 ∧ (f.row i).first = u.val ∧ (f.row i).second = u.val := by
      rw [sharedHere_iff]
      simp only [Fin.ext_iff,Fin.val_zero,tag,here,first,second]
      omega
    by_cases localPair : (f.row i).kind=0 ∧ (f.row i).first=u.val ∧ (f.row i).second=u.val
    · simp only [Range.choiceBits,sel.mpr localPair,ite_true,take,localPair]
      exact congrArg (fun z => List.ofFn (fun j : Fin z => bits i j.val)) len
    · simp only [Range.choiceBits,sel.not.mpr localPair,ite_false,take,localPair]
  have earlier (k : ℕ) (hk : k ≤ f.table.count) :
      tableChoiceBits (H u).rows (H u).team bits k = (List.range k).flatMap take := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [tableChoiceBits,List.range_succ,List.flatMap_append,ih (by omega),atRow k hk]
      simp
  rw [f.fullCount]
  exact earlier _ le_rfl

end TeamContraction

end BorderVNP
end Computability
end OAI
