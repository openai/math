import OAI.Computability.VPVNP.PairShrinkSurvivingOperands
import OAI.Computability.VPVNP.CompressorSlotWidth
import OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe

/-!
# Runtime pointers for surviving supply slices

The motif ordinal addresses a dense table of original CD arc numbers.
Recover the old base and lane, insert the role and subdivision digits, and
read the appropriate endpoint in the inverse sorted-field table. Removing
the direction digit gives the next state's actual port number.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkSurvivingPointers

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData
open CompressorRecords CompressorRecords.PhaseRecipe CompressorRecords.ShrinkSliceSweep
open ShrinkSurvivingFrames
open scoped Fin.CommRing

variable {w : ℕ} (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w)

/-- Runtime heads and dimensions of the retained shrinking tables. -/
structure Inputs where
  /-- Dense motif ordinal indexing both the absolute CD lookup and the four role-specific
  interval records. -/
  dense : Expr
  /-- Head of the table mapping each dense motif ordinal to its original CD arc number. -/
  absoluteHead : Expr
  /-- Head of the inverse sorted-slot table indexed by a surviving arc number and endpoint
  orientation. -/
  inverseHead : Expr
  /-- Number of remaining lanes used to split and reassemble the absolute CD arc address. -/
  lanes : Expr
  /-- Count of old base arcs used to displace a surviving arc's base number by its role
  ordinal. -/
  oldBases : Expr
  /-- Start of the dense motif-by-role records containing the subdivision interval frames. -/
  intervalHead : Expr

/-- Read the original CD arc number at the dense motif's entry in the absolute-index table. -/
def Inputs.absolute (H : Inputs) : Expr := .load (H.absoluteHead.add H.dense)

/-- Insert the role and subdivision between the old CD base and its absolute lane. -/
def Inputs.arc (H : Inputs) (subdiv : Fin 4 → ℕ) (t : Fin 4) (j : Fin (subdiv t)) : Expr :=
  let abs := H.absolute
  let base := (abs.div H.lanes).add (H.oldBases.mul (.lit t.val))
  let key := (base.mul (.lit (∑ i, subdiv i))).add (.lit j.val)
  (key.mul H.lanes).add (abs.mod H.lanes)

/-- Read a sorted endpoint from the inverse table at the two-field arc address. -/
def Inputs.rect (H : Inputs) (subdiv : Fin 4 → ℕ) (t : Fin 4)
    (j : Fin (subdiv t)) (dir : Bool) : Expr :=
  let field := ((H.arc subdiv t j).mul (.lit 2)).add (.lit dir.toNat)
  .load (H.inverseHead.add field)

/-- The sorted rows interleave outgoing and incoming owners at each site. -/
def port (degree : ℕ) (rect : Expr) : Expr :=
  let site := (rect.div (.lit degree)).div (.lit 2)
  (site.mul (.lit degree)).add (rect.mod (.lit degree))

/-- Dense ordinal and role address the interval bank. Its header includes
two totals, two singleton cells and two subdivision columns. -/
def Inputs.frame (H : Inputs) (subdiv : Fin 4 → ℕ) (t : Fin 4) (j : Fin (subdiv t)) : Expr :=
  let id := (H.dense.mul (.lit 4)).add (.lit t.val)
  let base := H.intervalHead.add (id.mul (.lit (5 + 7 * ∑ i, subdiv i)))
  base.add (.lit (5 + 2 * subdiv t + 3 * j.val))

variable {pub state mem}

private theorem eval_divmod (x y : Expr) {n d : ℕ} (hx : (x.eval pub state mem).val = n)
    (hy : (y.eval pub state mem).val = d) :
    (x.div y).eval pub state mem = ((n / d : ℕ) : Word w) ∧
      (x.mod y).eval pub state mem = ((n % d : ℕ) : Word w) := by
  change Fin.ofNat _ ((x.eval pub state mem).val / (y.eval pub state mem).val) = _ ∧
    Fin.ofNat _ ((x.eval pub state mem).val % (y.eval pub state mem).val) = _
  rw [hx, hy]
  exact ⟨rfl, rfl⟩

variable (H : Inputs)

/-- Removing the side bit from a represented sorted endpoint returns its
site-major slot ID. This calculation uses the actual word divisions. -/
theorem port_eval (rect : Expr) (degree site : ℕ) (side : Bool) (slot : Fin degree)
    (hd : degree < 2 ^ w) (htwo : 2 < 2 ^ w)
    (stored : (rect.eval pub state mem).val = (2 * site + side.toNat) * degree + slot.val) :
    (port degree rect).eval pub state mem = ((site * degree + slot.val : ℕ) : Word w) := by
  let owner := 2 * site + side.toNat
  have hlen : ((Expr.lit degree).eval pub state mem).val = degree := Nat.mod_eq_of_lt hd
  have ho : ((rect.div (.lit degree)).eval pub state mem).val = owner := by
    have hs := (eval_divmod rect (.lit degree) stored hlen).1
    have quotient : (owner * degree + slot.val) / degree = owner := by
      rw [Nat.mul_comm owner, Nat.mul_add_div (Nat.zero_lt_of_lt slot.isLt),
        Nat.div_eq_of_lt slot.isLt, Nat.add_zero]
    rw [show (rect.div (.lit degree)).eval pub state mem = _ from hs, quotient]
    exact Nat.mod_eq_of_lt (by
      have hle := Nat.div_le_self (owner * degree + slot.val) degree
      rw [quotient] at hle
      exact hle.trans_lt (stored ▸ (rect.eval pub state mem).isLt))
  have hmod := (eval_divmod rect (.lit degree) stored hlen).2
  have hs := (eval_divmod (rect.div (.lit degree)) (.lit 2) ho
    (show ((Expr.lit 2).eval pub state mem).val = 2 from Nat.mod_eq_of_lt htwo)).1
  have sideLt : side.toNat < 2 := by cases side <;> decide
  have quo : owner / 2 = site := by
    change (2 * site + side.toNat) / 2 = site
    rw [Nat.mul_add_div (by decide : 0 < 2), Nat.div_eq_of_lt sideLt, Nat.add_zero]
  rw [quo] at hs
  rw [Nat.mul_add_mod_of_lt slot.isLt] at hmod
  change ((rect.div (.lit degree)).div (.lit 2)).eval pub state mem * (degree : Word w) +
    (rect.mod (.lit degree)).eval pub state mem = _
  rw [hs, hmod, Nat.cast_add, Nat.cast_mul]


/-- Read the absolute arc field at the selected dense motif ordinal. -/
theorem absolute_eval {a g : ℕ} (X : State a (packingLaneBits a g)) (m : X.packingData.Motif)
    (base : Word w)
    (dense : H.dense.eval pub state mem = ((ShrinkMotifOrder.stateNumber X m).val : Word w))
    (head : H.absoluteHead.eval pub state mem = base)
    (room : base.val + (ShrinkMotifOrder.stateNumber X m).val < 2 ^ w)
    (directory : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber base mem) :
    (H.absolute.eval pub state mem).val =
      (MotifAbsolute.absoluteIndex X.slots X.baseIndex m.val).val := by
  let index := ShrinkMotifOrder.stateNumber X
  have cell := directory (index m)
  change (mem (base.val + (index m).val)).val =
    (MotifAbsolute.absoluteIndex X.slots X.baseIndex (index.symm (index m)).val).val at cell
  rw [index.symm_apply_apply] at cell
  change (mem (H.absoluteHead.eval pub state mem + H.dense.eval pub state mem).val).val = _
  rw [head, dense, Fin.val_add, Fin.val_natCast,
    Nat.mod_eq_of_lt (by dsimp only [index]; omega : (index m).val < 2 ^ w), Nat.mod_eq_of_lt room]
  exact cell

/-- Evaluate the physical inverse-table read from the two-component field address. -/
theorem rect_eval (subdiv : Fin 4 → ℕ) (t : Fin 4) (j : Fin (subdiv t)) (dir : Bool)
    (inverse arc : ℕ) (atBase : H.inverseHead.eval pub state mem = (inverse : Word w))
    (atArc : (H.arc subdiv t j).eval pub state mem = (arc : Word w))
    (fits : inverse + (2 * arc + dir.toNat) < 2 ^ w) :
    (H.rect subdiv t j dir).eval pub state mem = mem (inverse + (2 * arc + dir.toNat)) := by
  change mem (H.inverseHead.eval pub state mem +
    ((H.arc subdiv t j).eval pub state mem * (2 : Word w) + (dir.toNat : Word w))).val = _
  rw [atBase, atArc, ← Nat.cast_ofNat (R := Word w) (n := 2), ← Nat.cast_mul,
    ← Nat.cast_add, ← Nat.cast_add, mul_comm arc 2]
  congr 1
  exact Nat.mod_eq_of_lt fits

section Arc

variable {V H₀ Tag L : Type} {d c N J nL pad : ℕ}
variable [AddCommGroup H₀] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H₀ Tag L d c) (subdiv : Fin 4 → ℕ)
variable (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (lanes : L ≃ Fin nL)
variable (m : P.Motif) (t : Fin 4) (j : Fin (subdiv t))

/-- The genuine arc expression is the actual allocated rectangular record
number, with the original CD lane retained as its lowest digit. -/
theorem arc_eval
    (absolute : (H.absolute.eval pub state mem).val =
      (Slots.oldArcIndex P vertices tags lanes m.val).val)
    (laneCount : (H.lanes.eval pub state mem).val = nL)
    (bases : H.oldBases.eval pub state mem = (Slots.oldBaseArcCount N J d c : Word w)) :
    (H.arc subdiv t j).eval pub state mem =
      ((Slots.arcAddress P subdiv vertices tags lanes pad (.inl ⟨t, m, j⟩)).val : Word w) := by
  let i : Compression.SurvivingSlots.Id P.Motif subdiv := ⟨t, m, j⟩
  let old := P.baseMotifIndex vertices tags (P.baseMotif m)
  let l := lanes (P.sourceLane m)
  let stride := ∑ i, subdiv i
  have abs : (H.absolute.eval pub state mem).val = l.val + nL * old.val := absolute
  obtain ⟨div, mod⟩ := eval_divmod H.absolute H.lanes abs laneCount
  rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt l.isLt),
    Nat.div_eq_of_lt l.isLt, Nat.zero_add] at div
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt l.isLt] at mod
  have lanesWord : H.lanes.eval pub state mem = (nL : Word w) :=
    Fin.ext (laneCount.trans
      (Nat.mod_eq_of_lt (laneCount ▸ (H.lanes.eval pub state mem).isLt)).symm)
  have arc : (Slots.arcAddress P subdiv vertices tags lanes pad (.inl i)).val =
      ((old.val + Slots.oldBaseArcCount N J d c * t.val) * stride + j.val) * nL + l.val := by
    change l.val + nL * (j.val + stride * old.val +
      (Slots.oldBaseArcCount N J d c * stride) * t.val) = _
    ring
  rw [show (Slots.arcAddress P subdiv vertices tags lanes pad (.inl ⟨t, m, j⟩)).val = _ from arc]
  change (((H.absolute.div H.lanes).eval pub state mem +
    H.oldBases.eval pub state mem * (t.val : Word w))
      * (stride : Word w) + (j.val : Word w)) * H.lanes.eval pub state mem +
    (H.absolute.mod H.lanes).eval pub state mem = _
  rw [div, mod, bases, lanesWord]
  simp only [Nat.cast_add, Nat.cast_mul]

end Arc

/-- Exact frame address in the retained row for a dynamic dense motif ordinal. -/
theorem frame_eval {n A : ℕ} (T : Allocation w n A) (fit : T.Fits) (i : Fin n) (t : Fin 4)
    (j : Fin (T.subdiv t)) (dense : H.dense.eval pub state mem = (i.val : Word w))
    (interval : H.intervalHead.eval pub state mem = (T.widthEnd : Word w)) :
    (H.frame T.subdiv t j).eval pub state mem =
      (head (T.row (i, t)) (T.subdiv t) j : Word w) := by
  have base := (T.row_vals fit (i, t)).2.2.1
  have key : (Allocation.denseKey (i, t)).val = i.val * 4 + t.val := by
    change t.val + 4 * i.val = _
    omega
  change H.intervalHead.eval pub state mem +
    (H.dense.eval pub state mem * (4 : Word w) + (t.val : Word w)) *
      ((5 + 7 * ∑ i, T.subdiv i : ℕ) : Word w) + ((5 + 2 * T.subdiv t + 3 * j.val : ℕ) : Word w) = _
  rw [interval, dense, head, SliceSchedule.frameHead, base, Allocation.recordStart, key]
  simp only [Allocation.recordStride, Allocation.stride, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

end PairSimulation.ShrinkSurvivingPointers

end VPVNP
end Computability
end OAI
