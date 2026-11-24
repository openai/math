import OAI.Computability.VPVNP.RAMSortFieldIndex

/-!
# Loop bounds and word addresses for replaying a sorting stage

The validator enumerates the public phase and stride counters. It computes
each partner by a shift and xor, and computes the start of an incident
record field using a triangular layer number and a linear bit offset.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

@[simp] theorem length_strides {b a : ℕ} (ha : a ≤ b) (k : ℕ) (hk : k ≤ a) :
    (strides b a ha k hk).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [strides, ih]

/-- Exactly this many comparator layers are visited, regardless of the data. -/
@[simp] theorem length_phases {b : ℕ} (a : ℕ) (ha : a ≤ b) :
    (phases b a ha).length = (a + 1).choose 2 := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [phases, List.length_append, ih, length_strides,
      Nat.choose_succ_succ (a + 1) 1, Nat.choose_one_right, Nat.add_comm]

/-- A straight-line calculation of addresses and routing flags. Input
registers and public constants are available before this calculation. -/
inductive IndexExpr
  | arg (x : ℕ)
  | add (a b : IndexExpr)
  | sub (a b : IndexExpr)
  | mul (a b : IndexExpr)
  | div (a b : IndexExpr)
  | mod (a b : IndexExpr)
  | xor (a b : IndexExpr)
  | shl (a b : IndexExpr)
  | shr (a b : IndexExpr)

/-- Evaluate a sorting address or routing expression using natural-number arithmetic, shifts,
and exclusive-or. -/
def IndexExpr.eval : IndexExpr → ℕ
  | .arg x => x
  | .add a b => a.eval + b.eval
  | .sub a b => a.eval - b.eval
  | .mul a b => a.eval * b.eval
  | .div a b => a.eval / b.eval
  | .mod a b => a.eval % b.eval
  | .xor a b => a.eval ^^^ b.eval
  | .shl a b => a.eval <<< b.eval
  | .shr a b => a.eval >>> b.eval

/-- Count one operation for every binary node of the routing expression, treating its given
arguments as available registers. -/
def IndexExpr.work : IndexExpr → ℕ
  | .arg _ => 0
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b | .xor a b | .shl a b | .shr a b =>
      a.work + b.work + 1

/-- Arithmetic expressions for the current index, its comparator partner,
and the direction bit of the phase. -/
def wireIndex (h site off : ℕ) : IndexExpr := .add (.shl (.arg site) (.arg h)) (.arg off)
/-- Comparator partner index obtained by toggling bit j of the global wire index formed from
the site and offset. -/
def wirePartner (h site off j : ℕ) : IndexExpr := .xor (wireIndex h site off) (.shl (.arg 1) (.arg j))
/-- Extract bit a of the global wire index to determine ascending or descending order in phase
a. -/
def directionBit (h site off a : ℕ) : IndexExpr :=
  .mod (.shr (wireIndex h site off) (.arg a)) (.arg 2)

@[simp] theorem wireIndex_eval (h site off : ℕ) :
    (wireIndex h site off).eval = site * 2 ^ h + off := by
  simp [wireIndex, IndexExpr.eval, Nat.shiftLeft_eq]

@[simp] theorem wirePartner_eval (h site off j : ℕ) :
    (wirePartner h site off j).eval = partner j (site * 2 ^ h + off) := by
  simp [wirePartner, IndexExpr.eval, Nat.shiftLeft_eq, partner]

@[simp] theorem directionBit_eval (h site off a : ℕ) :
    decide ((directionBit h site off a).eval = 0) = phaseDirection a (site * 2 ^ h + off) := by
  simp [directionBit, IndexExpr.eval, Nat.shiftRight_eq_div_pow, phaseDirection]

/-- Linear bit address of the first bit of a single five-word record. The
two direction fields at each cross layer immediately follow the two
eight-word successor fields. -/
def fieldStart (h w a j dir off : ℕ) : IndexExpr :=
  let p := IndexExpr.sub (.sub (.arg a) (.arg h)) (.arg 1)
  let step := IndexExpr.sub (.sub (.arg a) (.arg j)) (.arg 1)
  let ord := IndexExpr.add (.div (.mul p (.add p (.arg 1))) (.arg 2)) step
  let width := IndexExpr.mul (.mul (.shl (.arg 1) (.arg h)) (.arg 5)) (.arg w)
  .add (.add (.mul (.arg 16) (.arg w)) (.mul (.add (.mul ord (.arg 2)) (.arg dir)) width))
    (.mul (.mul (.arg off) (.arg 5)) (.arg w))

theorem fieldStart_eval (h w a j dir off : ℕ) :
    (fieldStart h w a j dir off).eval =
      16 * w + ((((a-h-1) * ((a-h-1)+1) / 2 + (a-j-1)) * 2 + dir) *
        (2 ^ h * 5 * w)) + off * 5 * w := by
  simp [fieldStart, IndexExpr.eval, Nat.shiftLeft_eq]

/-- The straight-line address is the address in the allocation of equation
(10.1), including the offset of an individual bit inside its record. -/
theorem fieldStart_physical {h d H w : ℕ} (hw : 2 ^ h = 4 * H)
    (s : Stage (h+d)) (hc : h ≤ s.stride) (dir : Fin 2) (off : Fin (2 ^ h))
    (bit : Fin (5 * w)) :
    (fieldStart h w s.phase s.stride dir.val off.val).eval + bit.val =
      (RAMLayout.offset d H w (.inr (((crossStageEquiv h d).symm ⟨s, hc⟩), dir,
        ⟨off.val * 5 * w + bit.val, by
          have hoff : (off.val + 1) ≤ 4 * H := hw ▸ off.isLt
          have hb := Nat.mul_le_mul_right (5 * w) hoff
          have hbit := bit.isLt
          simp only [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc] at hb
          unfold RAMLayout.blockBits
          omega⟩))).val := by
  rw [fieldStart_eval, RAMLayout.offset_sort]
  simp only [crossStageEquiv, Equiv.coe_fn_symm_mk, RAMLayout.Layer.ordinal, RAMLayout.layerCount,
    Nat.choose_two_right, Nat.add_sub_cancel, RAMLayout.blockBits, hw]
  rw [Nat.mul_comm (s.phase - h - 1 + 1) (s.phase - h - 1)]
  ring

/-- Two address comparisons after computing all three expressions, even
when the current index is recomputed for each use. -/
theorem wireAddress_work (h site off j a : ℕ) :
    (wireIndex h site off).work + (wirePartner h site off j).work +
      (directionBit h site off a).work + 2 = 12 := rfl

@[simp] theorem fieldStart_work (h w a j dir off : ℕ) :
    (fieldStart h w a j dir off).work = 21 := rfl

end RAMSort

end VPVNP
end Computability
end OAI
