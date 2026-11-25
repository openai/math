import Mathlib.Tactic.FinCases
import OAI.ThreeFlat.RAM.TraceBucketLayout
import OAI.ThreeFlat.RAM.TraceOwnerFormula
import OAI.ThreeFlat.Diagonal.TraceSourceRectangle

namespace OAI
/-! # Region-size bounds for record generation on every physical source -/

namespace ThreeFlat.RAM.TraceBucketAtom
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TraceSourceOwner
open scoped Fin.CommRing

/-- All terms are global sites times a local word budget, a local lane
budget, or a published table endpoint. No two global site counts multiply. -/
def Layout.footprint (s : Layout) : ℕ :=
  40 + (s.depth+s.low+2) + (s.shape.header+2*s.shape.rows) +
    (s.shape.count+s.shape.rows*s.shape.stride+s.shape.rows*s.shape.track) + (s.relays+s.gates+s.tags+s.lowRows*s.shape.stride) +
    (s.bank+s.bank+2*s.lowRows) + (11*(s.shape.rows*s.slots)+4) +
    s.shape.rows + (1+2*s.depth) + s.slots +
    (s.equalId+s.zeroId+s.unitId) + (s.per+s.slots*3+s.shape.stride)

structure ImageCapacity {W : ℕ} (s : Layout) (m : Memory W) (b : ℕ) : Prop where
  rows : s.shape.rows=2^s.depth
  ticks : s.shape.header+s.shape.ticks ≤ 2*s.shape.rows
  hidden : 0<s.shape.count
  slots : 0<s.slots
  stride : 0<s.shape.stride
  size : s.footprint < 2^b
  recordEnd : s.records+11*(s.shape.rows*s.slots)+4 ≤ 2^W
  dictionaryEnd : s.dictionary+s.shape.rows ≤ 2^W
  maskEnd : s.masks+(1+2*s.depth) ≤ 2^W
  tableEnd : s.tableIds+s.slots ≤ 2^W
  margin : 5*b+128≤W
  masks : ∀ i, i<1+2*s.depth → (m (s.masks+i)).val < s.shape.rows
  sources : ∀ a i j, a<s.shape.rows → i<s.slots → j<4 →
    (m (s.readAt a i j)).val<2+s.shape.header+s.shape.count

theorem ImageCapacity.publicShape {W b : ℕ} {s : Layout} {m : Memory W} (h : ImageCapacity s m b) :
    ∀ i, TraceOwnerFormula.vars s.shape 1 0 0 i<2^b := by
  have size := h.size
  unfold Layout.footprint at size
  have nr : 0<s.shape.rows := by rw [h.rows]; exact Nat.two_pow_pos _
  have track := Nat.le_mul_of_pos_left s.shape.track nr
  have cnt : s.shape.count=s.shape.ticks*s.shape.cpu+(s.shape.layers*(s.shape.rows*s.shape.track)+
      ((s.shape.rows-1)*s.shape.edge+(s.shape.rows*s.shape.copy+s.shape.rows*s.shape.gates))) := rfl
  have str : s.shape.stride=2*s.shape.cpu+(s.shape.layers*s.shape.track+(s.shape.edge+(s.shape.copy+s.shape.gates))) := rfl
  intro i
  fin_cases i <;> dsimp [TraceOwnerFormula.vars] <;> omega

theorem vars_small (s : Shape) (b x y : ℕ) (hc : ∀ i,TraceOwnerFormula.vars s 1 0 0 i<2^b)
    (hx : x<2^b) (hy : y<2^b) : ∀ i, TraceOwnerFormula.vars s 1 x y i<2^b := by
  intro i
  have h := hc i
  fin_cases i <;> first | exact hx | exact hy | exact h

theorem owner_small (s : Shape) (fit : s.header+s.ticks≤2*s.rows) (hc : 0<s.count)
    {receiver address : ℕ} (hr : receiver<s.rows) (ha : address<2+s.header+s.count) :
    ownerAt s 1 receiver address<s.rows := by
  unfold ownerAt appendAt
  simp only [Nat.mul_one,Nat.div_one]
  split
  · exact hr
  · split
    · omega
    · exact (locate_spec s fit (show address-2-s.header<s.count by omega)).1

theorem ImageCapacity.capacity {W b} {s : Layout} {m : Memory W} (h : ImageCapacity s m b) :
    s.shape.count+s.shape.rows*s.shape.stride+1≤2^b := by
  have hs := h.size
  unfold Layout.footprint at hs
  omega

theorem ImageCapacity.records {W b} {s : Layout} {m : Memory W} (h : ImageCapacity s m b)
    {row slot leg : ℕ} (hr : row<s.shape.rows) (hs : slot<s.slots) (hj : leg<4) :
    s.readAt row slot leg<2^W := by
  have x := pack_lt hs hr
  have size := h.recordEnd
  unfold Layout.readAt
  omega

theorem ImageCapacity.two_power {W b} {s : Layout} {m : Memory W} (h : ImageCapacity s m b) :
    2^b≤(2:ℕ)^W := Nat.pow_le_pow_right (by decide) (by have := h.margin; omega)

theorem ImageCapacity.smallSource {W b} {s : Layout} {m : Memory W} (h : ImageCapacity s m b)
    {row slot leg : ℕ} (hr : row<s.shape.rows) (hs : slot<s.slots) (hj : leg<4) :
    (m (s.readAt row slot leg)).val<2^b := by
  have hv := h.sources row slot leg hr hs hj
  have hz := h.size
  unfold Layout.footprint at hz
  omega

end ThreeFlat.RAM.TraceBucketAtom

end OAI
