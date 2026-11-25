import OAI.Computability.BorderVNP.PackedDirectory
import OAI.Computability.BorderVNP.PackedTailCapacity

/-! # Bitwise correspondence for compact private and live demands -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory

/-- Every private bit is delivered once in one of the two possible tail pieces. The
source address is the original address in the concatenated reserved tails and the
destination is the proper offset at its assigned bundle/site. -/
theorem Layout.private_bit (d : Layout) (placed : ℕ → ℕ × ℕ) (j : ℕ)
    (ht : 0 < d.literal/2) (short : d.description ≤ d.literal/2) (bit : Fin d.description) :
    ∃! k : Fin 2, ∃ delta : ℕ,
      let row := d.privateRow placed j k
      delta < row.width ∧ row.cell = (placed j).1 ∧
        row.slot + delta = (placed j).2 + bit ∧
        (row.team * d.processors + row.processor)*(d.literal/2) +
          (row.offset + delta - (d.literal-d.literal/2)) = j*d.description + bit := by
  let start := j*d.description
  let tail := d.literal/2
  let sl (k : Fin 2) := slice start d.description tail k
  obtain ⟨k,hk,huniq⟩ := short_slice_cover (start := start) ht short bit
  have lower (x : Fin 2) : start ≤ (sl x).1 ∧ (start/tail+x)*tail ≤ (sl x).1 := by
    simp [sl,slice]
  refine ⟨k,⟨start+bit-(sl k).1,?_,rfl,?_,?_⟩,?_⟩
  · change start+bit-(sl k).1 < (sl k).2
    change (sl k).1 ≤ start+bit ∧ start+bit < (sl k).1 + (sl k).2 at hk
    omega
  · change (placed j).2 + ((sl k).1-start) + (start+bit-(sl k).1) = _
    have := (lower k).1
    change (sl k).1 ≤ start+bit ∧ _ at hk
    omega
  · let a := start/tail+k.val
    change (a/d.processors*d.processors+a%d.processors)*tail +
      (d.literal-tail+((sl k).1-a*tail)+(start+bit-(sl k).1)-(d.literal-tail)) = start+bit
    rw [Nat.div_add_mod' a d.processors]
    have hlow : a*tail ≤ (sl k).1 := (lower k).2
    change (sl k).1 ≤ start+bit ∧ _ at hk
    omega
  · rintro k' ⟨delta, hd, _, he, _⟩
    apply huniq
    change delta < (sl k').2 at hd
    change (placed j).2 + ((sl k').1-start) + delta = (placed j).2 + bit at he
    change (sl k').1 ≤ start+bit ∧ start+bit < (sl k').1 + (sl k').2
    have := (lower k').1
    omega

/-- Every bit of a literal or extra field is delivered in precisely one site-block
piece. Both offsets are measured in their actual ranges, and the block's placement
selects the receiving cell. -/
theorem Layout.live_bit (d : Layout) (placed : ℕ → ℕ × ℕ) (t p f : ℕ)
    (hb : 0 < d.block) (bit : Fin d.literal) :
    let start := p*d.stride + f*(d.literal+(d.teams-1)*d.link)
    let pos := start + bit
    let dest := placed (t*d.sites+pos/d.block)
    ∃! k : Fin (d.literal/d.block+2), ∃ delta : ℕ,
      let row := d.liveRow placed t p f k
      delta < row.width ∧ row.offset + delta = bit ∧ row.cell = dest.1 ∧
        row.slot + delta = dest.2 + pos%d.block := by
  dsimp only
  let start := p*d.stride + f*(d.literal+(d.teams-1)*d.link)
  let sl (k : ℕ) := slice start d.literal d.block k
  let pos := start + bit
  obtain ⟨k,hk,hu⟩ := slice_cover (start := start) hb bit
  have h : (sl k).1 ≤ pos ∧ pos < (sl k).1+(sl k).2 := hk
  have hi := (mem_slice_iff ..).mp hk
  have hp : pos / d.block = start/d.block+k.val := by
    apply Nat.le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hb).mpr (by simpa [Nat.succ_mul] using hi.2.2.2))
    · exact (Nat.le_div_iff_mul_le hb).mpr hi.2.2.1
  have hlo : start ≤ (sl k).1 ∧ (start/d.block+k.val)*d.block ≤ (sl k).1 := by simp [sl,slice]
  refine ⟨k, ⟨pos-(sl k).1,?_,?_,?_,?_⟩,?_⟩
  · change pos-(sl k).1 < (sl k).2
    omega
  · change (sl k).1-start + (pos-(sl k).1) = bit.val
    dsimp [pos] at *
    omega
  · change (placed (t*d.sites + (start/d.block+k.val))).1 = (placed (t*d.sites+pos/d.block)).1
    rw [hp]
  · change (placed (t*d.sites+(start/d.block+k.val))).2 + ((sl k).1-(start/d.block+k.val)*d.block) +
      (pos-(sl k).1) = (placed (t*d.sites+pos/d.block)).2 + pos%d.block
    have hm := Nat.div_add_mod' pos d.block
    rw [hp] at hm ⊢
    omega
  · rintro k' ⟨delta,hd,he,_,_⟩
    apply hu
    change delta < (sl k').2 at hd
    change (sl k').1-start + delta = bit.val at he
    have hlow : start ≤ (sl k').1 := by simp [sl,slice]
    change (sl k').1 ≤ start+bit ∧ start+bit < (sl k').1+(sl k').2
    omega

/-- With the consecutive initial-site slot allocation, all three passes together inspect
at most eight candidates per team and initial site, independently of the bit widths. -/
theorem Layout.candidates_le (d : Layout) (hb : 0 < d.block) (fields : d.fields ≤ 2)
    (room : d.processors*d.literal ≤ d.sites*d.block) (sites : d.processors ≤ d.sites)
    (entries : d.entries ≤ d.teams*d.sites) : d.candidates ≤ 8*(d.teams*d.sites) := by
  have hmul : (d.processors*(d.literal/d.block))*d.block ≤ d.sites*d.block := by
    rw [Nat.mul_assoc]
    exact (Nat.mul_le_mul_left _ (Nat.div_mul_le_self ..)).trans room
  have hpieces : d.processors*(d.literal/d.block+2) ≤ 3*d.sites := by
    have h := Nat.le_of_mul_le_mul_right hmul hb
    rw [Nat.mul_add]
    omega
  calc
    d.candidates = 2*d.entries + (d.teams*d.fields)*(d.processors*(d.literal/d.block+2)) := by
      unfold candidates; ring
    _ ≤ 2*(d.teams*d.sites) + (d.teams*2)*(3*d.sites) := Nat.add_le_add
      (Nat.mul_le_mul_left _ entries) (Nat.mul_le_mul (Nat.mul_le_mul_left _ fields) hpieces)
    _ = _ := by ring

/-- Reading a private source through the concatenated processor tails returns the
original bit in the bundle/site description, with the same row-major offset as the router. -/
theorem Layout.private_storage (d : Layout) (fits : d.entries*d.description ≤ d.teams*d.processors*(d.literal/2))
    (strings : Fin d.entries → Fin d.description → Bool) (j : Fin d.entries) (b : Fin d.description) :
    let width : Fin d.entries → ℕ := fun _ => d.description
    let cap : ∑ x, width x ≤ d.teams*d.processors*(d.literal/2) := by simpa [width] using fits
    let a := tailAddress width cap ⟨j,b⟩
    (finProdFinEquiv a).val = j.val*d.description+b.val ∧ storeTails width strings a = strings j b := by
  dsimp only
  refine ⟨?_,read_stored_bit ..⟩
  rw [tailAddress_linear]
  simp

end Packing.Directory

end BorderVNP
end Computability
end OAI
