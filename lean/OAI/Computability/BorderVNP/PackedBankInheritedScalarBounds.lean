import OAI.Computability.BorderVNP.PackedInheritedLayerEmit
import OAI.Computability.BorderVNP.PackedBankInheritedScalarCapacity
import OAI.Computability.BorderVNP.PackedBankPacketFields

/-! # Scalar word bounds for retained interval records

The base of an empty clipped interval may equal the bank extent. Inclusive
endpoint bounds control that stored base as well as the other eight scalar
fields. Retaining a layer takes the maximum of the old bound and the new
extent. Final placement adds the cell's bit or box prefix once.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open CellSparse
open scoped Classical
open private record_fields from OAI.Computability.BorderVNP.CellPacketFields

/-- Upper bound on each actual frozen scalar word, before final placement. -/
def Site.ScalarBound (s : Site) (U : ℕ) : Prop := ∀ a ∈ s.markedWords, a.2 ≤ U

/-- Erasing relocation tags gives the canonical unplaced packet words of the same row. -/
theorem marked_values (r : Record) : (marked r).map Prod.snd = Packet.record r := by
  have port (p : Port) : p.shift 0 = p := by cases p; simp [Port.shift]
  have route (t : Route) : t.shift 0 = t := by cases t; simp [Route.shift,port]
  have original : (r.shift 0).rebaseBox 0 = r := by
    cases r <;> simp [Record.shift,Record.rebaseBox,port,route]
  have tag (a : Kind × ℕ) : a.1.move 0 0 a.2 = a.2 := by rcases a with ⟨k,n⟩; cases k <;> simp [Kind.move]
  simpa only [tag,original] using marked_move 0 0 r

/-- Raw bounds on all birth records give a bound on their frozen words, including the ABI tags. -/
theorem Site.scalarBound_of_recordFields (s : Site) {U : ℕ} (h : ∀ r ∈ s.rows, Packet.RecordFields r U) :
    s.ScalarBound (max 3 U) := by
  intro a ha
  obtain ⟨r,hr,hw⟩ := List.mem_flatMap.mp ha
  apply record_fields r (h r hr)
  rw [← marked_values]
  exact List.mem_map.mpr ⟨a,hw,rfl⟩

/-- Both absolute starts and the width fit the new site extent, including an empty interval. -/
theorem Slice.bases_le (p : Slice) (s : Site) {n : ℕ}
    (h₁ : p.oldStart+p.width ≤ s.incoming) (h₂ : p.newStart+p.width ≤ n) :
    s.work+p.oldStart ≤ s.size+n ∧ s.size+p.newStart ≤ s.size+n ∧ p.width ≤ s.size+n := by
  unfold Site.size
  omega

/-- Each of the nine marked command fields fits the successor extent or the unit tag. -/
theorem Slice.marked_le (p : Slice) (s : Site) {n : ℕ}
    (h₁ : p.oldStart+p.width ≤ s.incoming) (h₂ : p.newStart+p.width ≤ n) :
    ∀ a ∈ marked (p.record s), a.2 ≤ max 1 (s.size+n) := by
  intro a ha
  have hb := p.bases_le s h₁ h₂
  change a ∈ [(Kind.plain,1),(.plain,1),(.plain,p.width),(.bitAddress,s.work+p.oldStart),
    (.plain,0),(.plain,1),(.bitAddress,s.size+p.newStart),(.plain,0),(.plain,1)] at ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-- The new history preserves the old scalar bound and adds fields bounded by the
actual successor extent. The maximum introduces no multiplicative factor per retention. -/
theorem Site.scalarBound_retain (s : Site) {U n : ℕ} (old : s.ScalarBound U) {cuts : List Slice}
    (h₁ : ∀ p ∈ cuts, p.oldStart+p.width ≤ s.incoming) (h₂ : ∀ p ∈ cuts, p.newStart+p.width ≤ n) :
    (s.retain n cuts).ScalarBound (max U (max 1 (s.size+n))) := by
  intro a ha
  rw [s.markedWords_retain,List.mem_append] at ha
  rcases ha with ho | hn
  · exact (old a ho).trans (le_max_left ..)
  · obtain ⟨p,hp,ha⟩ := List.mem_flatMap.mp hn
    exact (p.marked_le s (h₁ p hp) (h₂ p hp) a ha).trans (le_max_right ..)

/-- Final placement adds at most one prefix to a marked scalar. -/
theorem Kind.move_le (tag : Kind) (off base u : ℕ) : tag.move off base u ≤ max off base+u := by
  cases tag <;> simp only [Kind.move] <;> omega

/-- Raw scalar values of all final records, with their real bit and box offsets. -/
theorem Site.placed_scalar_le (s : Site) {U : ℕ} (h : s.ScalarBound U) (off base : ℕ) :
    ∀ a ∈ (s.placedRows off base).flatMap Packet.record, a ≤ max off base+U := by
  intro a ha
  rw [← s.markedWords_move] at ha
  obtain ⟨⟨tag,n⟩,hn,rfl⟩ := List.mem_map.mp ha
  exact (tag.move_le off base n).trans (Nat.add_le_add_left (h _ hn) _)

/-- Every final sparse row meets the physical packet decoder's field bound. -/
theorem Site.placed_recordFields (s : Site) {U : ℕ} (h : s.ScalarBound U) (off base : ℕ)
    (r : Record) (hr : r ∈ s.placedRows off base) : Packet.RecordFields r (max off base+U) :=
  BankCharges.recordFields_of_words r _ fun a ha => s.placed_scalar_le h off base a (List.mem_flatMap.mpr ⟨r,hr,ha⟩)

/-- The site packet's row-count prefix also fits, together with the final placed fields. -/
theorem Site.placed_packet_le (s : Site) {U : ℕ} (h : s.ScalarBound U) (off base : ℕ) :
    ∀ a ∈ Packet.fieldList Packet.record (s.placedRows off base), a ≤ max s.rows.length (max off base+U) := by
  intro a ha
  change a ∈ (s.placedRows off base).length :: _ at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · simp [Site.placedRows]
  · exact (s.placed_scalar_le h off base a ha).trans (le_max_right ..)

namespace Layer

open Crossing Shortening Shortening.CombiningStep InheritedBank

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
  {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
  {S : Type} [Fintype S] (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
  (binName : S → ℕ) (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
  (v : p.layout.Site) {old next np : ℕ} (oldID : p.layout.Edge ↪ Fin old)
  (nextID : (output e p bin perm positive first q).layout.Edge ↪ Fin next) (portID : P ↪ Fin np)

local notation3 "outN" => (output e p bin perm positive first q).layout
local notation3 "cutRow" => layerSlice e p bin perm binName positive first q v oldID nextID portID
local notation3 "inc" => incoming outN (.inl v)

/-- Each selected physical row satisfies the two addition guards required by the
fixed-width emitter, even if the row has zero lanes and starts at the bank end. -/
theorem slice_emit_room (r : LayerRow p v) (s : Site) (hin : s.incoming = incoming p.layout v)
    {w : ℕ} (hroom : max 1 (s.size+inc) < 2^w) :
    1 < 2^w ∧ s.work+(cutRow r).oldStart < 2^w ∧ s.size+(cutRow r).newStart < 2^w := by
  have cover := layer_covers e p bin perm binName positive first q v oldID nextID portID
  have member := (mem_layerCuts e p bin perm binName positive first q v oldID nextID portID).mpr ⟨r,rfl⟩
  have bound := (cutRow r).bases_le s ((cover.oldFit _ member).trans_eq hin.symm) (cover.newFit _ member)
  have hsize : s.size+inc < 2^w := (le_max_right ..).trans_lt hroom
  exact ⟨(le_max_left ..).trans_lt hroom,bound.1.trans_lt hsize,bound.2.1.trans_lt hsize⟩

/-- Exact guard of the arithmetic command once the public operands denote this physical row.
The expanded local record capacity pays for both additions at the selected output site. -/
theorem command_room (r : LayerRow p v) (s : Site) (prior payload : p.layout.Site → ℕ)
    (hin : s.incoming = incoming p.layout v) (hwork : s.work ≤ payload v)
    (test : (outN).Site → Prop) (hv : test (.inl v)) {w : ℕ}
    (hroom : localRecords outN true (nextPrior e p bin perm positive first q prior)
      (nextPayload e p bin perm positive first q payload) test < 2^w)
    (x : Arg → ℕ) (hrow : command x = (cutRow r).record s) :
    1 < 2^w ∧ x .work+(x .oldBase+x .clip) < 2^w ∧ x .extent+x .newBase < 2^w := by
  have room := (retained_extent_le e p bin perm positive first q v s prior payload hin hwork test hv).trans_lt hroom
  have bounds := slice_emit_room e p bin perm binName positive first q v oldID nextID portID r s hin room
  have left : x .work+(x .oldBase+x .clip) = s.work+(cutRow r).oldStart :=
    congrArg (fun z : Record => match z with | .equal _ _ a _ => a.base | _ => 0) hrow
  have right : x .extent+x .newBase = s.size+(cutRow r).newStart :=
    congrArg (fun z : Record => match z with | .equal _ _ _ b => b.base | _ => 0) hrow
  exact ⟨bounds.1,left ▸ bounds.2.1,right ▸ bounds.2.2⟩

/-- All previous scalar words and every newly selected equality fit the maximum of the
previous bound and the actual expanded local record load of the current tested region. -/
theorem retained_scalarBound (s : Site) {U : ℕ} (old : s.ScalarBound U) (prior payload : p.layout.Site → ℕ)
    (hin : s.incoming = incoming p.layout v) (hwork : s.work ≤ payload v)
    (test : (outN).Site → Prop) (hv : test (.inl v)) (cuts : List Slice)
    (sorted : cuts.Perm (layerCuts e p bin perm binName positive first q v oldID nextID portID)) :
    (s.retain inc cuts).ScalarBound (max U (localRecords outN true
      (nextPrior e p bin perm positive first q prior) (nextPayload e p bin perm positive first q payload) test)) := by
  have cover := covers_perm sorted (layer_covers e p bin perm binName positive first q v oldID nextID portID)
  have extent := retained_extent_le e p bin perm positive first q v s prior payload hin hwork test hv
  have h := s.scalarBound_retain old (fun c hc => (cover.oldFit c hc).trans_eq hin.symm) cover.newFit
  exact fun a ha => (h a ha).trans (max_le_max_left _ extent)

/-- On the emitted list in public row order, a common cap on old words and the
current tile suffices unchanged. Only the final placement prefix is added. -/
theorem ordered_placed_fields (s : Site) {U : ℕ} (old : s.ScalarBound U) (prior payload : p.layout.Site → ℕ)
    (hin : s.incoming = incoming p.layout v) (hwork : s.work ≤ payload v)
    (test : (outN).Site → Prop) (hv : test (.inl v))
    (cap : localRecords outN true (nextPrior e p bin perm positive first q prior)
      (nextPayload e p bin perm positive first q payload) test ≤ U) (off base : ℕ) :
    let site := s.retain inc (orderedCuts p oldID portID v e bin perm binName positive first q nextID)
    ∀ r ∈ site.placedRows off base, Packet.RecordFields r (max off base+U) := by
  intro site
  have h := retained_scalarBound e p bin perm binName positive first q v oldID nextID portID s old
    prior payload hin hwork test hv _ (ordered_perm p oldID portID v e bin perm binName positive first q nextID)
  have bound : site.ScalarBound U := fun a ha => (h a ha).trans (max_le le_rfl cap)
  exact site.placed_recordFields bound off base

end Layer
end Packing.Inherited

end BorderVNP
end Computability
end OAI
