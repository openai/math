import OAI.Computability.BorderVNP.CubeLabelProducerVolumes
import OAI.Computability.BorderVNP.PackedDirectoryOccupiedRoom
import OAI.Computability.BorderVNP.TransmissionDataAddresses
import OAI.Computability.BorderVNP.TransmissionSourceRegion

/-! # Word range of the seven fields of every populated delivery row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory

/-- The fitted ends of the source arrays and the occupied receiving intervals
bound every word actually emitted in the compact directory. -/
theorem Layout.populated_words_fit_of_slabs (d : Layout) (pp lp : ℕ → ℕ × ℕ)
    (bounds : d.DestinationBounds) (fields : 0 < d.fields)
    (tails : d.entries*d.description ≤ d.teams*d.processors*(d.literal/2))
    {W : ℕ} (teamsFit : d.teams ≤ 2^W) (procFit : d.processors ≤ 2^W)
    (fieldFit : d.fields ≤ 2^W) (literalFit : d.literal < 2^W)
    (cellFit : ∀ key, (d.keyPlacement pp lp key).1 < 2^W)
    (endFit : ∀ key, (d.keyPlacement pp lp key).2 + d.keyWidth key ≤ 2^W)
    (i : Fin (d.directory pp lp).length) :
    ∀ a ∈ (d.directory pp lp)[i.val].words, a < 2^W := by
  let r := (d.directory pp lp)[i.val]
  have mem : r ∈ d.directory pp lp := List.getElem_mem i.isLt
  obtain ⟨j,hj,row,pos⟩ := (d.mem_directory_iff pp lp r).mp mem
  have team := (d.populated_team pp lp bounds.processors fields tails mem).trans_le teamsFit
  have ⟨proc,last⟩ := d.populated_source_bounds pp lp mem bounds.processors
    (e := r.width-1) (by omega)
  have procWord := proc.trans_le procFit
  have field : r.field < d.fields := by
    rw [← row]
    by_cases p : j < 2*d.entries
    · simpa only [Layout.row,p,ite_true,Layout.privateRow] using fields
    · simp only [Layout.row,p,ite_false,Layout.liveRow]
      exact Nat.mod_lt _ fields
  have fieldWord := field.trans_le fieldFit
  let b : d.CandidateBit pp lp := ⟨⟨j,hj⟩,⟨0,by change 0 < (d.row pp lp j).width; rwa [row]⟩⟩
  let x := d.destinationKey pp lp bounds b
  obtain ⟨hc,hs⟩ := d.destinationKey_placement pp lp bounds b
  change (d.row pp lp j).cell = (d.keyPlacement pp lp x.1).1 at hc
  change (d.row pp lp j).slot + 0 = (d.keyPlacement pp lp x.1).2 + x.2.val at hs
  rw [row] at hc hs
  have cellWord := hc ▸ cellFit x.1
  have slotWord := (Nat.add_lt_add_left x.2.isLt (d.keyPlacement pp lp x.1).2).trans_le (endFit x.1)
  change ∀ a ∈ r.words, a < 2^W
  intro a ha
  simp only [Row.words,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with h|h|h|h|h|h|h <;> omega

/-- The polynomial room used by the native candidate loop also bounds the compact
output words. Placement offsets are inspected only at true private and live entries. -/
private theorem polynomial_fit (d : Layout) (pp lp : ℕ → ℕ × ℕ)
    (bounds : d.DestinationBounds) (fields : 0 < d.fields)
    (tails : d.entries*d.description ≤ d.teams*d.processors*(d.literal/2))
    {W cells pb lb extent : ℕ} (cellsFit : cells ≤ 2^W)
    (legal : ∀ key, (d.keyPlacement pp lp key).1 < cells)
    (occupied : ∀ k, (d.keyPlacement pp lp k).2 ≤ extent)
    (room : ISA.wordBound (ISA.placementBound d pb lb extent) < 2^W)
    (i : Fin (d.directory pp lp).length) :
    ∀ a ∈ (d.directory pp lp)[i.val].words, a < 2^W := by
  let B := ISA.placementBound d pb lb extent
  have scalar : B < 2^W := by
    apply lt_of_le_of_lt _ room
    change B ≤ 32*(B+1)^4
    nlinarith [Nat.zero_le (B^4), Nat.zero_le (B^3), Nat.zero_le (B^2)]
  have teamsPos : 0 < d.teams := Nat.zero_lt_of_lt
    (d.populated_team pp lp bounds.processors fields tails (List.getElem_mem i.isLt))
  have tp : d.teams ≤ d.teams*d.processors :=
    Nat.le_mul_of_pos_right d.teams bounds.processors
  have pt : d.processors ≤ d.teams*d.processors :=
    Nat.le_mul_of_pos_left d.processors teamsPos
  have both : d.teams*d.processors ≤ d.teams*d.processors*d.fields :=
    Nat.le_mul_of_pos_right _ fields
  have allFields : d.fields ≤ d.teams*d.processors*d.fields :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos teamsPos bounds.processors)
  have pieces : d.teams*d.processors*d.fields ≤ d.candidates :=
    (Nat.le_mul_of_pos_right _ (show 0 < d.literal/d.block+2 from Nat.zero_lt_succ _)).trans (Nat.le_add_left ..)
  have candidates : d.candidates ≤ B := by dsimp [B,ISA.placementBound]; omega
  have literal : d.literal ≤ B := by dsimp [B,ISA.placementBound]; omega
  apply d.populated_words_fit_of_slabs pp lp bounds fields tails
    (tp.trans (both.trans (pieces.trans (candidates.trans scalar.le))))
    (pt.trans (both.trans (pieces.trans (candidates.trans scalar.le))))
    (allFields.trans (pieces.trans (candidates.trans scalar.le))) (literal.trans_lt scalar)
    (fun k => (legal k).trans_le cellsFit) _ i
  intro k
  apply le_trans _ scalar.le
  have offset := occupied k
  cases k <;> dsimp only [Layout.keyWidth] <;> dsimp only [B,ISA.placementBound] <;> omega

/-- The polynomial room used by the native candidate loop also bounds the compact
output words. Placement offsets are inspected only at true private and live entries. -/
theorem Layout.populated_words_fit (d : Layout) (pp lp : ℕ → ℕ × ℕ)
    (bounds : d.DestinationBounds) (fields : 0 < d.fields)
    (tails : d.entries*d.description ≤ d.teams*d.processors*(d.literal/2))
    {W cells pb lb extent : ℕ} (cellsFit : cells ≤ 2^W)
    (legal : ∀ key, (d.keyPlacement pp lp key).1 < cells)
    (privateRoom : ∀ j < d.entries, (pp j).2 ≤ extent)
    (liveRoom : ∀ a < d.teams*d.sites, (lp a).2 ≤ extent)
    (room : ISA.wordBound (ISA.placementBound d pb lb extent) < 2^W)
    (i : Fin (d.directory pp lp).length) :
    ∀ a ∈ (d.directory pp lp)[i.val].words, a < 2^W :=
  polynomial_fit d pp lp bounds fields tails cellsFit legal (fun key => by
    cases key with
    | inl j => exact privateRoom j.val j.isLt
    | inr pair =>
      obtain ⟨t,s⟩ := pair
      have lim := Nat.mul_le_mul_right d.sites t.isLt
      rw [Nat.succ_mul] at lim
      have hsite := s.isLt
      exact liveRoom (t.val*d.sites+s.val) (by omega)) room i

/-- In the physical bank image, both the row owner and its occupied offset follow
from the placement certificate and the actual per-cell size of the supplied data. -/
theorem BankPlacement.populated_words_fit {d : Layout} {pp lp : ℕ → ℕ × ℕ}
    {A : Type*} [Fintype A] {cells : ℕ} {cell : A → Fin cells} {id : A ↪ ℕ} {width : A → ℕ}
    (place : BankPlacement d pp lp A cell id width)
    (bounds : d.DestinationBounds) (fields : 0 < d.fields)
    (tails : d.entries*d.description ≤ d.teams*d.processors*(d.literal/2))
    {W pb lb extent : ℕ} (cellsFit : cells ≤ 2^W)
    (size : ∀ c, DataSlabs.size cell width c ≤ extent)
    (room : ISA.wordBound (ISA.placementBound d pb lb extent) < 2^W)
    (i : Fin (d.directory pp lp).length) :
    ∀ a ∈ (d.directory pp lp)[i.val].words, a < 2^W :=
  polynomial_fit d pp lp bounds fields tails cellsFit
    (fun k => by rw [place.entry k]; exact (cell (place.key k)).isLt)
    (fun k => by
      rw [place.entry k]
      exact (Nat.le_add_right ..).trans ((DataSlabs.base_end_le cell id width (place.key k)).trans (size _)))
    room i

end Packing.Directory

end BorderVNP
end Computability
end OAI
