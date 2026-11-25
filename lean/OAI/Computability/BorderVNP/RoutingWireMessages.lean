import OAI.Computability.BorderVNP.RoutingCapacity
import OAI.Computability.BorderVNP.RoutingISAAddressProof

/-! # A bijection on the actual exterior wire assignment

For an unordered pair the RAM layout concatenates the common prefix, the leg
with the lower-numbered endpoint, the opposite leg, and the zero-padding
suffix. The two-leg order and the quotients agree with the computed addresses.
This identifies the physical processor-by-partner bit variables with precisely
the message variables used in the multiplicity proof.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Routing

/-- A leg starts at an endpoint distinct from its relay. -/
theorem hop_ne_relay {R : ℕ} {hR : 2 < R} {width : Fin R → Fin R → ℕ}
    {u v : Fin R} (p : Hop hR width u v) : u ≠ v := by
  obtain ⟨j,i,hi⟩ := p
  by_cases h : u = j
  · simp only [pairBits,dite_eq_right (not_ne_iff.mpr h),Finset.notMem_empty] at hi
  · rw [pairBits,dite_eq_left h] at hi
    exact (Finset.mem_filter.mp hi).2 ▸ (relay_ne_endpoints hR h i).1.symm

/-- Geometry of the four consecutive regions in every unordered physical block. -/
structure WireLayout (R r link : ℕ) where
  /-- Enough teams for a nonempty relay pool. -/
  three : 2 < R
  /-- All teams use the same public unordered demand lists. -/
  width : Fin R → Fin R → ℕ
  /-- Length of the common broadcast in each block. -/
  header : ℕ
  /-- Both directed uses and the header fit in the real physical block. -/
  fits (b : Block R) : header + legLoad three width b.val.1 b.val.2 +
    legLoad three width b.val.2 b.val.1 ≤ r*link

namespace WireLayout

variable {R r link : ℕ} (L : WireLayout R r link)

/-- The number of unused physical bits on one block. -/
def slack (b : Block R) : ℕ :=
  r*link-(L.header+legLoad L.three L.width b.val.1 b.val.2+legLoad L.three L.width b.val.2 b.val.1)

/-- Every unused physical bit carries its unordered block and its suffix index. -/
abbrev Padding := (b : Block R) × Fin (L.slack b)

/-- The logical variable occupying a word of the physical unordered block. -/
abbrev Slot (b : Block R) :=
  Fin L.header ⊕ Hop L.three L.width b.val.1 b.val.2 ⊕
  Hop L.three L.width b.val.2 b.val.1 ⊕ Fin (L.slack b)

/-- The four regions, in the exact order tested by the word RAM. -/
def position (b : Block R) : L.Slot b ≃ Fin (r*link) :=
  let hi := (Equiv.sumCongr (legEquiv L.three L.width b.val.2 b.val.1) (Equiv.refl _)).trans finSumFinEquiv
  let lo := (Equiv.sumCongr (legEquiv L.three L.width b.val.1 b.val.2) hi).trans finSumFinEquiv
  ((Equiv.sumCongr (Equiv.refl _) lo).trans finSumFinEquiv).trans (finCongr (by
    dsimp [slack]
    have := L.fits b
    omega))

/-- Header bits occupy the unshifted prefix. -/
theorem position_header (b : Block R) (i : Fin L.header) :
    (L.position b (.inl i)).val = i.val := rfl

/-- Ordinal of a used leg with the lower team as its endpoint. -/
theorem position_low (b : Block R) (p : Hop L.three L.width b.val.1 b.val.2) :
    (L.position b (.inr (.inl p))).val = L.header + (legEquiv L.three L.width _ _ p).val := rfl

/-- Ordinal of a used leg with the higher team as its endpoint. -/
theorem position_high (b : Block R) (p : Hop L.three L.width b.val.2 b.val.1) :
    (L.position b (.inr (.inr (.inl p)))).val =
      L.header + (legLoad L.three L.width b.val.1 b.val.2 + (legEquiv L.three L.width _ _ p).val) := rfl

/-- Unused bits start immediately after both complete legs. -/
theorem position_padding (b : Block R) (i : Fin (L.slack b)) :
    (L.position b (.inr (.inr (.inr i)))).val =
      L.header + (legLoad L.three L.width b.val.1 b.val.2 +
        (legLoad L.three L.width b.val.2 b.val.1 + i.val)) := rfl

/-- The actual bit-coordinate space, per block, is processor number times
local link position in row-major order. -/
def coordinates (b : Block R) : L.Slot b ≃ Fin r × Fin link :=
  (L.position b).trans finProdFinEquiv.symm

/-- The typed message value in each of the four regions. -/
def regionValues (m : Messages L.three L.width (Fin L.header → Bool) L.Padding)
    (b : Block R) : L.Slot b → Bool :=
  Sum.elim (m.broadcast b) (Sum.elim (m.hop b.val.1 b.val.2)
    (Sum.elim (m.hop b.val.2 b.val.1) (fun i ↦ m.padding ⟨b,i⟩)))

/-- Recover a typed message from the bit values on the four regions. -/
def fromRegions (value : (b : Block R) → L.Slot b → Bool) :
    Messages L.three L.width (Fin L.header → Bool) L.Padding where
  broadcast b i := value b (.inl i)
  hop u v p := if h : u < v then value ⟨(u,v),h⟩ (.inr (.inl p))
    else if h' : v < u then value ⟨(v,u),h'⟩ (.inr (.inr (.inl p)))
    else false
  padding i := value i.1 (.inr (.inr (.inr i.2)))

private theorem values_fromRegions (value : (b : Block R) → L.Slot b → Bool) :
    L.regionValues (L.fromRegions value) = value := by
  funext b s
  rcases s with a | a | a | a
  · rfl
  · simp [regionValues,fromRegions,b.property]
  · simp [regionValues,fromRegions,b.property,not_lt.mpr b.property.le]
  · rfl

private theorem from_regionValues (m : Messages L.three L.width (Fin L.header → Bool) L.Padding) :
    L.fromRegions (L.regionValues m) = m := by
  cases m with
  | mk broadcast hop pad =>
    unfold fromRegions
    congr 1
    funext u v p
    rcases lt_or_gt_of_ne (hop_ne_relay p) with h | h
    · simp [regionValues,h]
    · simp [regionValues,h,not_lt.mpr h.le]

/-- No physical wire bits or message variables are gained or lost when
partitioning the actual exterior array into common headers, both legs, and padding. -/
def exteriorEquiv : (Block R × Fin r × Fin link → Bool) ≃
    Messages L.three L.width (Fin L.header → Bool) L.Padding where
  toFun ext := L.fromRegions (fun b s ↦ ext (b,L.coordinates b s))
  invFun m := fun x ↦ L.regionValues m x.1 ((L.coordinates x.1).symm x.2)
  left_inv ext := by
    funext x
    dsimp only
    rw [L.values_fromRegions]
    simp
  right_inv m := by
    have h : (fun b s ↦ L.regionValues m b ((L.coordinates b).symm (L.coordinates b s))) =
        L.regionValues m := by funext b s; simp
    dsimp only
    rw [h,L.from_regionValues]

/-- Every logical term has exactly one actual exterior bit assignment, with
all unused wire bits forced to zero by the checked message conditions. -/
theorem existsUnique_exterior (fixedBlock : Block R) (header : Fin L.header → Bool)
    (sourceHigh : Fin R → Fin R → ℕ → Bool) (payload : Fin R → Fin R → ℕ → Bool) :
    ∃! ext : Block R × Fin r × Fin link → Bool,
      Checks L.three L.width fixedBlock header sourceHigh payload (L.exteriorEquiv ext) := by
  obtain ⟨m,valid,unique⟩ := existsUnique_messages (Pad := L.Padding) L.three L.width fixedBlock
    header sourceHigh payload
  exact ⟨L.exteriorEquiv.symm m,by simpa using valid, fun ext h ↦
    L.exteriorEquiv.injective (by simpa using unique (L.exteriorEquiv ext) h)⟩

end WireLayout
end Routing

end BorderVNP
end Computability
end OAI
