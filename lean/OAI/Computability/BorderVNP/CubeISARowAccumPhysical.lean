import OAI.Computability.BorderVNP.CubeISARowAccumDecoder
import OAI.Computability.BorderVNP.CubeISARowAccumSingleton

/-! # Native row totals for the actual selected packet and singleton

A packet decodes its selector into scratch words and tallies their directions.
The row postcondition gives the genuine physical crossing count, while the
decoded edge ordinals remain available for subsequent local vertex processing.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.RowAccum

open RoutingISA VPVNP.BurstRAM Physical Tally

/-- Decode the whole physical selector, then accumulate the actual local crossing widths. -/
def packetFromSelector : RoutingISA.Code := .seq decodeLoop packetLoop

/-- A packet contributes its precise physical counts to the contiguous array and
leaves the canonical edge ordinals in scratch. All other memory words are preserved. -/
theorem packetFromSelector_run {w n d blocks K h : ℕ} (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (r : Bank w) (m : Memory w) (base src b s : ℕ)
    (select : Packet n d blocks → Selector n K h) (p : Packet n d blocks)
    (rsel : (r 43).val = (selectorOrder n K h (select p)).val)
    (radix : (r 44).val = Fintype.card (Edge (n+1)))
    (rb : (r 45).val = base) (rd : (r 46).val = n+1) (rs : (r 47).val = src)
    (rh : (r 48).val = h) (rwth : (r 49).val = s)
    (room : base+(n+1) ≤ 2^w) (scratch : src+h ≤ 2^w)
    (separate : src+h ≤ base ∨ base+(n+1) ≤ src)
    (fit : ∀ j < n+1, readings m (base+j) + h*s < 2^w) :
    BoundedRun pub macros packetFromSelector r m (15*h+7) (fun z =>
      (∀ j : Fin (n+1), z.mem (base+j) = readings m (base+j) + crossCount b s select (.inl p) j) ∧
      (∀ i : Fin h, z.mem (src+i) = (edgeOrder (n+1) ((select p).2 i)).val) ∧
      ∀ a, (a < base ∨ base+(n+1) ≤ a) → (a < src ∨ src+h ≤ a) → z.mem a = readings m a) := by
  let u := select p
  let E := Fintype.card (Edge (n+1))
  let raw := (selectorOrder n K h u).val
  have decode := decodeLoop_run pub macros r m src E h raw rsel radix rs rh Fintype.card_pos scratch
  rw [show 15*h+7 = (6*h+4)+(9*h+3) by omega]
  apply decode.seq
  intro t mt hd
  obtain ⟨hmem,keep⟩ := hd
  change readings mt = digitImage (readings m) src E raw h at hmem
  have decoded (k : Fin h) : readings mt (src+k) = (edgeOrder (n+1) (u.2 k)).val := by
    rw [hmem,digitImage,ite_eq_left (by have := k.isLt; omega),Nat.add_sub_cancel_left]
    exact selectorOrder_digit u k
  have untouched (a : ℕ) (ha : a < src ∨ src+h ≤ a) : readings mt a = readings m a := by
    rw [hmem,digitImage,ite_eq_right (by omega)]
  have rowOld (j : ℕ) (hj : j < n+1) : readings mt (base+j) = readings m (base+j) :=
    untouched _ (by omega)
  let dir k := (mt (src+k)).val % (n+1)
  have count := packetLoop_run pub macros t mt base (n+1) src h s
    ((keep 45 (by decide)).trans rb) ((keep 46 (by decide)).trans rd)
    ((keep 47 (by decide)).trans rs) ((keep 48 (by decide)).trans rh)
    ((keep 49 (by decide)).trans rwth) (Nat.succ_pos n) room scratch separate
    (fun j hj => (rowOld j hj).symm ▸ fit j hj)
  apply count.mono le_rfl
  intro z hz
  change z.mem = packetImage (readings mt) base s dir h at hz
  have directions (i : Fin h) : dir i = ((select p).2 i).2.val := by
    change readings mt (src+i) % (n+1) = _
    rw [decoded,edgeOrder_mod]
  have outside (a : ℕ) (ha : a < base ∨ base+(n+1) ≤ a) : z.mem a = readings mt a := by
    have no (k : ℕ) : a ≠ base+dir k := by have : dir k < n+1 := Nat.mod_lt _ (Nat.succ_pos n); omega
    simp [hz,packetImage,no]
  refine ⟨fun j => ?_, fun i => (outside (src+i) (by have := i.isLt; omega)).trans (decoded i),
    fun a ha hb => (outside a ha).trans (untouched a hb)⟩
  rw [hz,packetImage_crossCount b s base select p _ _ directions,rowOld _ j.isLt]

/-- The row update for a physical singleton reads its original ordered endpoints
and preserves the complement of the row array, including other singleton slots. -/
theorem singlePhysical_run {w n d blocks K h : ℕ} (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (r : Bank w) (m : Memory w) (base b s : ℕ)
    (select : Packet n d blocks → Selector n K h) (slot : SingleSlot n d blocks (h*b))
    (rb : (r 45).val = base) (rdim : (r 46).val = n+1) (rd : (r 47).val = d)
    (rx : (r 24).val = (finFunctionFinEquiv slot.1.val.1).val)
    (ry : (r 25).val = (finFunctionFinEquiv slot.1.val.2).val)
    (room : base+(n+1) ≤ 2^w)
    (fit : ∀ j : Fin (n+1), readings m (base+j) + crossCount b s select (.inr slot) j < 2^w) :
    BoundedRun pub macros singleLoop r m (13*(n+1)+5) (fun z =>
      (∀ j : Fin (n+1), z.mem (base+j) = readings m (base+j) + crossCount b s select (.inr slot) j) ∧
      ∀ a, a < base ∨ base+(n+1) ≤ a → z.mem a = readings m a) := by
  have pos : 0 < d := Nat.zero_lt_of_lt (slot.1.val.1 0).isLt
  have safe (j : ℕ) (hj : j < n+1) :
      readings m (base+j) + unequalDigit d (finFunctionFinEquiv slot.1.val.1)
        (finFunctionFinEquiv slot.1.val.2) j < 2^w := by
    have he := unequalDigit_crossCount b s select slot (⟨j,hj⟩ : Fin (n+1))
    rw [show j = (⟨j,hj⟩ : Fin (n+1)).val from rfl,he]
    exact fit ⟨j,hj⟩
  apply (singleLoop_run pub macros r m base (n+1) d _ _ rb rdim rd rx ry pos room safe).mono le_rfl
  intro z hz
  refine ⟨fun j => ?_,fun a ha => ?_⟩
  · rw [hz,singleImage_crossCount]
  · rw [hz,singleImage,ite_eq_right (by omega),Nat.add_zero]

end Cube.RowAccum

end BorderVNP
end Computability
end OAI
