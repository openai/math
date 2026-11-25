import OAI.Computability.BorderVNP.TransmissionPinsInput

/-! # Physical exterior reads from the initialized processor tapes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Pins

open VPVNP BurstRAM

/-- Processor containing a flat bit position of an exterior link. -/
def Layout.exteriorProcessor (L : Layout) (pos : ℕ) (hpos : pos < L.processors * L.link) :
    Fin L.processors :=
  ⟨pos / L.link, (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (by
    intro h
    simp [h] at hpos))).2 hpos⟩

namespace ProcessorFields

variable {L : Layout} (r : ProcessorFields L)

/-- The processor's exterior string for the designated partner. Its slot in the
input tape skips the calling team. -/
def exteriorBlock (i : Fin L.processors) (partner : ℕ) : List Bool :=
  (r.exterior i)[if partner < L.team then partner else partner - 1]?.getD []

/-- The physical link address selects the intended processor, exterior string
and bit inside that string in the flattened initialization stream. -/
theorem header_exterior (partner pos : ℕ) (ht : L.team < L.teams) (hp : partner < L.teams)
    (hd : partner ≠ L.team) (hpos : pos < L.processors * L.link) :
    r.header[physicalBitAddress L.team L.teams L.literal L.link partner pos]? =
      (r.exteriorBlock (L.exteriorProcessor pos hpos) partner)[pos % L.link]? := by
  let i := L.exteriorProcessor pos hpos
  let k := if partner < L.team then partner else partner - 1
  have hk : k < L.teams - 1 := by dsimp [k]; split <;> omega
  have hk' : k < (r.exterior i).length := r.exterior_count i ▸ hk
  have hj : pos % L.link < L.link := Nat.mod_lt _ (by
    by_contra! h
    simp [show L.link = 0 by omega] at hpos)
  let off := k * L.link + pos % L.link
  have hoff : off < (L.teams - 1) * L.link := by
    have h := Nat.mul_le_mul_right L.link (Nat.succ_le_of_lt hk)
    rw [Nat.succ_mul] at h
    dsimp [off]
    omega
  have hrow : L.literal + off < L.stride := by unfold Layout.stride Layout.offset; omega
  have addr : physicalBitAddress L.team L.teams L.literal L.link partner pos =
      i.val * L.stride + (L.literal + off) := by
    simp only [physicalBitAddress, i, Layout.exteriorProcessor, Layout.stride, Layout.offset, off, k]
    ring
  rw [addr, header, getElem?_rows r.row r.row_length i _ hrow, row, TeamTapeInput.inputData]
  have hpre : L.literal + off < (r.literal i ++ (r.exterior i).flatten).length := by
    rw [List.length_append, r.literal_length, r.exterior_length]
    omega
  rw [List.getElem?_append_left hpre,
    List.getElem?_append_right (by rw [r.literal_length]; omega), r.literal_length,
    Nat.add_sub_cancel_left]
  change (r.exterior i).flatten[k * L.link + pos % L.link]? =
    ((r.exterior i)[k]?.getD [])[pos % L.link]?
  rw [RAMSort.getElem?_flatten_rect (r.link_length i) hk' hj, List.getElem?_eq_getElem hk']
  rfl

/-- Every valid exterior address falls inside the complete processor header. -/
theorem exterior_address_lt_header (partner pos : ℕ) (ht : L.team < L.teams)
    (hp : partner < L.teams) (hd : partner ≠ L.team) (hpos : pos < L.processors * L.link) :
    physicalBitAddress L.team L.teams L.literal L.link partner pos < r.header.length := by
  have hl : 0 < L.link := Nat.pos_of_ne_zero (by intro h; simp [h] at hpos)
  obtain ⟨hq, _, hu⟩ := physicalBitAddress_bounds (literal := L.literal) ht hp hd hl hpos
  have hs : 2 * L.literal + (L.teams - 1) * L.link = L.stride := by
    unfold Layout.stride Layout.offset
    omega
  have hh := Nat.mul_le_mul_right L.stride (Nat.succ_le_of_lt hq)
  rw [Nat.succ_mul] at hh
  rw [hs] at hu
  rw [r.header_length]
  have : L.literal + (L.teams - 1) * L.link ≤ L.stride := by
    unfold Layout.stride Layout.offset
    omega
  omega

/-- Any memory preserving the initialized processor input reads this exterior word,
including after boot or scratch stores above the header. -/
theorem ContainsInput.exterior {w : ℕ} {r : ProcessorFields L} {m : Memory w}
    (h : r.ContainsInput m) (partner pos : ℕ) (ht : L.team < L.teams)
    (hp : partner < L.teams) (hd : partner ≠ L.team) (hpos : pos < L.processors * L.link) :
    m (physicalBitAddress L.team L.teams L.literal L.link partner pos) =
      TeamTapeInputEmit.headerWord w (r.exteriorBlock (L.exteriorProcessor pos hpos) partner)
        (pos % L.link) := by
  rw [h _ (r.exterior_address_lt_header partner pos ht hp hd hpos)]
  simp only [TeamTapeInputEmit.headerWord, r.header_exterior partner pos ht hp hd hpos]

/-- The checker’s actual time-zero memory reads the addressed exterior bit
as the word encoding of the partner string at the link remainder. -/
theorem initialized_exterior (w partner pos : ℕ) (ht : L.team < L.teams)
    (hp : partner < L.teams) (hd : partner ≠ L.team) (hpos : pos < L.processors * L.link) :
    RAMMemory.initialMemory r.header.length (TeamTapeInputEmit.headerWord w r.header)
        (physicalBitAddress L.team L.teams L.literal L.link partner pos) =
      TeamTapeInputEmit.headerWord w (r.exteriorBlock (L.exteriorProcessor pos hpos) partner)
        (pos % L.link) :=
  (r.containsInput_initial w).exterior partner pos ht hp hd hpos

end ProcessorFields

end RoutingISA.Pins

end BorderVNP
end Computability
end OAI
