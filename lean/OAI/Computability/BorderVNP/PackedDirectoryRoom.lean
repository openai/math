import OAI.Computability.BorderVNP.PackedDirectoryProgram

/-! # A polynomial word range suffices for every placement-directory operation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.ISA

/-- A common bound for public parameters, array indices and the stored cell offsets.
Only the second word of a descriptor is subsequently used in address arithmetic. -/
structure Sizes (d : Layout) (pb lb : ℕ) (pp lp : ℕ → ℕ × ℕ) (B : ℕ) : Prop where
  /-- All enumerated candidate indices. -/
  candidates : d.candidates ≤ B
  /-- Processor literal width. -/
  literal : d.literal ≤ B
  /-- Padded private-description width. -/
  description : d.description ≤ B
  /-- Width of an initial site block. -/
  block : d.block ≤ B
  /-- Number of sites. -/
  sites : d.sites ≤ B
  /-- Consecutive slot distance between processors. -/
  stride : d.stride ≤ B
  /-- Offset of the extra field after literal and exterior inputs. -/
  extraStart : d.literal+(d.teams-1)*d.link ≤ B
  /-- The two placement-table base addresses. -/
  bases : pb ≤ B ∧ lb ≤ B
  /-- The offsets actually fetched in the private and live placement arrays, including
  the unused terminal candidates. -/
  offsets : (∀ j ≤ B, (pp j).2 ≤ B) ∧ (∀ j ≤ B^2+(2*B^2+B), (lp j).2 ≤ B)

/-- A common polynomial in the public scalar bounds for all intermediate words. -/
def wordBound (B : ℕ) : ℕ := 32*(B+1)^4

private theorem poly_bound (B : ℕ) :
    2*B^2+B ≤ wordBound B ∧ (2*B^2+B)*B + 2*B ≤ wordBound B ∧
    B+(B^2+(2*B^2+B))*2+1 ≤ wordBound B ∧ 2*B^2+B+B ≤ wordBound B := by
  unfold wordBound
  repeat' apply And.intro
  all_goals nlinarith [Nat.zero_le (B^4),Nat.zero_le (B^3),Nat.zero_le (B^2)]

private theorem geometry_bound {w B start len block step : ℕ} (hstart : start ≤ 2*B^2)
    (hlen : len ≤ B) (hb : 0 < block) (hblock : block ≤ B) (hstep : step ≤ B)
    (room : wordBound B < 2^w) :
    EndpointsFit w start len block step ∧
      B + max start ((start/block+step)*block) < 2^w ∧ start/block+step ≤ 2*B^2+B := by
  have hi := Nat.add_le_add ((Nat.div_le_self start block).trans hstart) hstep
  have hl := Nat.mul_le_mul hi hblock
  obtain ⟨hp,hq,_,_⟩ := poly_bound B
  refine ⟨⟨hb,hi.trans_lt (hp.trans_lt room),?_,?_⟩,?_,hi⟩ <;> omega

/-- The test used by the native traversal follows for every candidate from one
quartic address bound. There is no hypothesis about an execution or a trace. -/
theorem candidates_fit {d : Layout} {w B pb lb : ℕ} {pp lp : ℕ → ℕ × ℕ}
    (size : Sizes d pb lb pp lp B) (tailPos : 0 < d.literal/2) (blockPos : 0 < d.block)
    (room : wordBound B < 2^w) (i : ℕ) (hi : i < d.candidates) :
    if i < 2*d.entries then LayoutFitsPrivate d w pb pp i else LayoutFitsLive d w lb lp i := by
  have hI := hi.le.trans size.candidates
  obtain ⟨_,_,address,_⟩ := poly_bound B
  by_cases h : i < 2*d.entries
  · rw [ite_eq_left h]
    let j := i/2
    let start := j*d.description
    have hj : j ≤ B := (Nat.div_le_self ..).trans hI
    have hs : start ≤ 2*B^2 := by
      have := Nat.mul_le_mul hj size.description
      dsimp only [start]; rw [sq]; omega
    have ht : d.literal/2 ≤ B := (Nat.div_le_self ..).trans size.literal
    obtain ⟨ends,off,_⟩ := geometry_bound hs size.description tailPos ht ((Nat.mod_le i 2).trans hI) room
    have a : pb+j*2+1 < 2^w := by
      have hp := size.bases.1
      omega
    have hd := size.offsets.1 j hj
    have hl := size.literal
    exact ⟨ends,a,(Nat.add_le_add_right hl _).trans_lt off,(Nat.add_le_add_right hd _).trans_lt off⟩
  · rw [ite_eq_right h]
    let j := i-2*d.entries
    let k := d.literal/d.block+2
    let u := j/k
    let a := u/d.fields
    let t := a/d.processors
    let p := a%d.processors
    let f := u%d.fields
    let start := p*d.stride+f*(d.literal+(d.teams-1)*d.link)
    let site := start/d.block+j%k
    let entry := t*d.sites+site
    have hj : j ≤ B := (Nat.sub_le ..).trans hI
    have hu : u ≤ B := (Nat.div_le_self ..).trans hj
    have ha : a ≤ B := (Nat.div_le_self ..).trans hu
    have ht : t ≤ B := (Nat.div_le_self ..).trans ha
    have hproc : p ≤ B := (Nat.mod_le ..).trans ha
    have hf : f ≤ B := (Nat.mod_le ..).trans hu
    have hstart : start ≤ 2*B^2 := by
      have hl := Nat.mul_le_mul hproc size.stride
      have hr := Nat.mul_le_mul hf size.extraStart
      dsimp only [start]; rw [sq]; omega
    obtain ⟨ends,off,hsite⟩ := geometry_bound hstart size.literal blockPos size.block ((Nat.mod_le ..).trans hj) room
    have he : entry ≤ B^2+(2*B^2+B) := by
      dsimp only [entry,site]
      rw [sq]
      simpa only [sq] using Nat.add_le_add (Nat.mul_le_mul ht size.sites) hsite
    have hd := size.offsets.2 entry he
    have hl := size.bases.2
    refine ⟨ends,by change lb+entry*2+1 < 2^w; omega,?_⟩
    exact (Nat.add_le_add hd (Nat.sub_le ..)).trans_lt off

end Packing.Directory.ISA

end BorderVNP
end Computability
end OAI
