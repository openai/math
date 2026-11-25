import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Nonoverlapping dated banks on the checked original address tape -/

namespace Hierarchy.ProtocolRAM.Calendar.PrefixWidths
/-- Every dated bank has room for its entire word-addressable edge vector and a
separate sentinel word for the clamped destination in the sparse native scan. -/
structure Layout (edges : ℕ) where
  archive : ℕ
  bits : ℕ
  scratch : ℕ
  covered : edges≤2^bits

namespace Layout
variable {edges : ℕ} (L : Layout edges)

def bank (date : ℕ) : Bank := ⟨L.archive+date*(2^L.bits+1),L.bits⟩

theorem archive_le (date : ℕ) : L.archive≤(L.bank date).base := Nat.le_add_right ..

theorem before {i j : ℕ} (lt : i<j) : (L.bank i).base+edges < (L.bank j).base := by
  have bound := Nat.mul_le_mul_right (2^L.bits+1) (show i+1≤j from lt)
  rw [Nat.add_mul,one_mul] at bound
  have extent := L.covered
  change L.archive+i*(2^L.bits+1)+edges<L.archive+j*(2^L.bits+1)
  omega

/-- The shared temporary scan arena starts just beyond the last dated bank. -/
def packed (edges archive bits last : ℕ) (covered : edges≤2^bits) : Layout edges :=
  ⟨archive,bits,archive+(last+1)*(2^bits+1),covered⟩

theorem packed_scratch (archive bits last : ℕ) (covered : edges≤2^bits) (j : ℕ) (hj : j≤last) :
    let layout := packed edges archive bits last covered
    (layout.bank j).base+edges<layout.scratch := by
  intro layout
  exact layout.before (Nat.lt_succ_of_le hj)

/-- The temporary words used by the width pass may be reused by the reserve phase.
Its two permanent banks per date begin just after every permanent width page. -/
def reserveLayout {count : ℕ} (L : Layout edges) (axesBits last : ℕ) (covered : count≤2^axesBits) :
    Layout count := packed count (L.bank (last+1)).base axesBits (2*last+1) covered

theorem reserve_after {count : ℕ} (axesBits last : ℕ) (axes : count≤2^axesBits) :
    (L.bank last).base+edges≤(L.reserveLayout axesBits last axes).archive :=
  (L.before (Nat.lt_succ_self last)).le

theorem reserve_temporary {count : ℕ} (axesBits last : ℕ) (axes : count≤2^axesBits) {j : ℕ} (hj : j≤last) :
    let R := L.reserveLayout axesBits last axes
    (R.bank (2*j+1)).base+count≤R.scratch :=
  (packed_scratch (L.bank (last+1)).base axesBits (2*last+1) axes (2*j+1) (by omega)).le

theorem reserve_scratch {count : ℕ} (axesBits last : ℕ) (axes : count≤2^axesBits) :
    (L.reserveLayout axesBits last axes).scratch =
      L.archive+(last+1)*(2^L.bits+1)+(2*last+2)*(2^axesBits+1) := rfl

/-- Choosing the minimal public dyadic fields keeps the whole permanent range
linear in the source edge/axis counts, including empty arrays. -/
theorem dense_extent (edges axes archive last : ℕ) :
    let lw := packed edges archive (edges.log2+1) last ((Nat.lt_log2_self (n:=edges)).le)
    let lr := lw.reserveLayout (axes.log2+1) last (count:=axes) ((Nat.lt_log2_self (n:=axes)).le)
    lr.scratch≤archive+(last+1)*(2*edges+3)+(2*last+2)*(2*axes+3) := by
  intro lw lr
  have rounded (x : ℕ) : 2^(x.log2+1)+1≤2*x+3 := by
    by_cases empty : x=0
    · simp [empty]
    · have small := Nat.log2_self_le empty
      rw [pow_succ]
      omega
  change archive+(last+1)*(2^(edges.log2+1)+1)+(2*last+2)*(2^(axes.log2+1)+1)≤_
  exact Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left _ (rounded edges)) archive)
    (Nat.mul_le_mul_left _ (rounded axes))

end Layout
end Hierarchy.ProtocolRAM.Calendar.PrefixWidths

end OAI
