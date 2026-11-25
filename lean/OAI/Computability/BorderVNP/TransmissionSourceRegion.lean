import OAI.Computability.BorderVNP.TransmissionSiteStrings

/-! # Every populated literal or pin source is in its initialized processor array -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory

open BorderVNP.RoutingISA
open private tail_field_bounds from OAI.Computability.BorderVNP.TransmissionSiteStrings
open private literal_address_lt from OAI.Computability.BorderVNP.TransmissionSources

private theorem live_offset (d : Layout) (lp : ℕ → ℕ × ℕ) (t p f k e : ℕ)
    (he : e < (d.liveRow lp t p f k).width) : (d.liveRow lp t p f k).offset + e < d.literal := by
  let a := p*d.stride+f*(d.literal+(d.teams-1)*d.link)
  let s := slice a d.literal d.block k
  change e < s.2 at he
  obtain ⟨_,hi,_,_⟩ := (mem_slice_iff a d.literal d.block k (s.1+e)).mp
    ⟨Nat.le_add_right ..,Nat.add_lt_add_left he _⟩
  change s.1+e < a+d.literal at hi
  change s.1-a+e < d.literal
  have h : a ≤ s.1 := le_max_left ..
  omega

/-- Compaction can remove empty slices, but every represented bit refers to a true
processor and to a fitted lane of its source field. -/
theorem Layout.populated_source_bounds (d : Layout) (pp lp : ℕ → ℕ × ℕ) {r : Row}
    (hr : r ∈ d.directory pp lp) (hp : 0 < d.processors) {e : ℕ} (he : e < r.width) :
    r.processor < d.processors ∧ r.offset+e < d.literal := by
  obtain ⟨i,_,rfl,_⟩ := (d.mem_directory_iff pp lp r).mp hr
  by_cases part : i < 2*d.entries <;> simp only [row,part,ite_true,ite_false] at he ⊢
  · exact ⟨Nat.mod_lt _ hp,(tail_field_bounds d pp _ _ _ he).2⟩
  · exact ⟨Nat.mod_lt _ hp,live_offset d lp _ _ _ _ _ he⟩

/-- Source-address protection requires just the ends of the processor input and
substitution arrays, uniformly in all populated data rows. -/
theorem Layout.source_below (d : Layout) (pp lp : ℕ → ℕ × ℕ) {r : Row}
    (hr : r ∈ d.directory pp lp) (hp : 0 < d.processors) {e : ℕ} (he : e < r.width)
    (L : Pins.Layout) (processors : d.processors = L.processors) (literal : d.literal = L.literal)
    (origin : ℕ) (input : L.processors*L.stride ≤ origin) (substitute : L.ibase+L.count ≤ origin) :
    r.sourceBase L + e < origin := by
  obtain ⟨pproc,off⟩ := d.populated_source_bounds pp lp hr hp he
  rw [processors] at pproc
  rw [literal] at off
  by_cases fld : r.field = 0
  · simpa [Row.sourceBase,fld,Nat.add_assoc] using (literal_address_lt L pproc off).trans_le input
  · have h : r.processor*L.literal+(r.offset+e) < L.count :=
      (Nat.add_lt_add_left off _).trans_le ((Nat.succ_mul _ _).symm ▸ Nat.mul_le_mul_right L.literal pproc)
    simpa [Row.sourceBase,fld,Nat.add_assoc] using (Nat.add_lt_add_left h L.ibase).trans_le substitute

end Packing.Directory

end BorderVNP
end Computability
end OAI
