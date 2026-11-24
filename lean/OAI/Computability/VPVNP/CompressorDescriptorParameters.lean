import OAI.Computability.VPVNP.CompressorFormulaRow
import OAI.Computability.VPVNP.CompressorRecordsCursorParameterBounds
import OAI.Computability.VPVNP.CompressorRecordsLevelFields

/-!
# Computing the cursor input frame in the tight descriptor layout

The chronological row count is already in the workspace at offset eight.
From that count the pair-ABI program recovers the number of compression
blocks, the lane exponent and the first level address. It places eight raw
words in the active frame. Their destination points to eight persistent
scalar cells in the first level, starting at offset six.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DescriptorParameters

open BurstRAM BurstRAM.PrivateRAM CursorBounds DescriptorSpace PhaseRecipe
open CursorRAM.ParametersInit
open scoped Fin.CommRing

variable {w : ℕ}

/-- The formula compiler uses the actual pair ABI's workspace, input length and address width. -/
def operand : Fin 5 → Fin 11 := ![2, 6, 7, 2, 2]

private def base : Expr := .publicWord 0
private def count : Expr := .load (base.add (.lit 8))
private def directory (g : ℕ) := base.add (.lit (11+g))
/-- Expression locating the first level header immediately after the calendar's fixed-width
directory rows. -/
def firstLevel (g : ℕ) := (directory g).add (count.mul (.lit (g+3)))
/-- Expression locating the persistent cursor bank six words into the first level header. -/
def persistentBank (g : ℕ) := (firstLevel g).add (.lit 6)
/-- Recover the number of complete repeated blocks from the published row count. -/
def calendarBlocks (initial phases : ℕ) := (count.sub (.lit initial)).div (.lit phases)

private def laneExponent (initial phases lanes : ℕ) := (calendarBlocks initial phases).mul (.lit lanes)

/-- Eight published raw words consumed by the cursor parameter program. -/
def raw (F : Shape) (a initial phases lanes : ℕ) : FormulaRow 5 where
  dest := base.add (.lit 9)
  fields := ![.publicWord 1, .publicWord 2, .lit a, laneExponent initial phases lanes,
    directory F.arity, .lit 1, (firstLevel F.arity).add (.lit (F.scalarFields+6+F.tables)),
    persistentBank F.arity]

/-- The pair ABI exposes all the operands of the native frame publisher. -/
def table (F : Shape) (a initial phases lanes : ℕ) :=
  LiveStageLink.widen (raw F a initial phases lanes).recipe.table (Function.Embedding.refl _) operand

private theorem word_eq {v : Word w} {n : ℕ} (hv : v.val = n) : v = (n : Word w) := by
  subst n
  exact Fin.ext (Nat.mod_eq_of_lt v.isLt).symm

/-- Inputs available at normal entry after the calendar has published its count. -/
structure Ready (L : Layout) (B n initial phases T : ℕ) (pub : Fin 11 → Word w) (m : Memory w) : Prop where
  workspace : (pub 2).val = L.base
  length : (pub 6).val = n
  address : (pub 7).val = addressBits B n
  total : (m (pub 2+8).val).val = initial + T*phases
  layoutCount : directoryRows L = initial + T*phases
  phase_pos : 0 < phases
  phase_fit : phases < 2^w

theorem eval_level {L B n initial phases T pub m} (h : Ready (w := w) L B n initial phases T pub m)
    (s : Word w) :
    (firstLevel L.shape.arity).eval (pub ∘ operand) s m = (levelStart L 0 : Word w) := by
  change pub 2 + ((11+L.shape.arity : ℕ) : Word w) +
    m (pub 2+8).val * ((L.shape.arity+3 : ℕ) : Word w) = _
  rw [word_eq h.total, word_eq h.workspace]
  simp only [levelStart, Nat.zero_mul, Nat.add_zero, levelsBase, directoryBase, plannerTag, frameBase,
    h.layoutCount, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

private theorem eval_lanes {L B n initial phases T pub m} (h : Ready (w := w) L B n initial phases T pub m)
    (s : Word w) (lanes : ℕ) :
    (laneExponent initial phases lanes).eval (pub ∘ operand) s m = (T*lanes : ℕ) := by
  let c := m (pub 2+8).val
  have ht : c.val = initial + T*phases := h.total
  have hi : (initial : Word w).val = initial := Nat.mod_eq_of_lt
    ((Nat.le_add_right ..).trans_lt (ht ▸ c.isLt))
  have hsub : (c-(initial : Word w)).val = T*phases := by
    rw [Fin.sub_val_of_le (by change (initial : Word w).val ≤ c.val; omega), ht, hi, Nat.add_sub_cancel_left]
  have hdiv : (BinaryOp.div.eval (c-(initial : Word w)) (phases : Word w)).val = T := by
    change ((c-(initial : Word w)).val / (phases : Word w).val) % (2^w) = T
    rw [hsub, show (phases : Word w).val = phases from Nat.mod_eq_of_lt h.phase_fit,
      Nat.mul_div_cancel _ h.phase_pos, Nat.mod_eq_of_lt]
    exact (Nat.le_mul_of_pos_right _ h.phase_pos).trans_lt
      ((Nat.le_add_left ..).trans_lt (ht ▸ c.isLt))
  change BinaryOp.div.eval (c-(initial : Word w)) (phases : Word w) * (lanes : Word w) = _
  rw [word_eq hdiv, Nat.cast_mul]

theorem eval_blocks {L B n initial phases T pub m} (h : Ready (w := w) L B n initial phases T pub m)
    (s : Word w) : (calendarBlocks initial phases).eval (pub ∘ operand) s m = (T : Word w) := by
  have eqn := eval_lanes h s 1
  change (calendarBlocks initial phases).eval (pub ∘ operand) s m * 1 = ((T*1 : ℕ) : Word w) at eqn
  simpa using eqn

/-- The row's eight native word expressions are exactly the raw cursor parameters. -/
theorem raw_values {L B n initial phases T pub m} (h : Ready (w := w) L B n initial phases T pub m)
    (s : Word w) (a lanes : ℕ) :
    (fun i ↦ ((raw L.shape a initial phases lanes).fields i).eval (pub ∘ operand) s m) =
      (fun i ↦ CursorRAM.encode w
        (inputValues n (addressBits B n) a (T*lanes) (directoryBase L) 1 (incidenceStart L 0)
          (levelStart L 0+6) i)) := by
  funext i
  fin_cases i
  · exact word_eq h.length
  · exact word_eq h.address
  · rfl
  · exact eval_lanes h s lanes
  · change pub 2 + ((11+L.shape.arity : ℕ) : Word w) = ((directoryBase L : ℕ) : Word w)
    rw [word_eq h.workspace]
    simp only [directoryBase, plannerTag, frameBase, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  · rfl
  · change (firstLevel L.shape.arity).eval (pub ∘ operand) s m +
      ((L.shape.scalarFields+6+L.shape.tables : ℕ) : Word w) = ((incidenceStart L 0 : ℕ) : Word w)
    rw [eval_level h, incidenceStart, levelHeaderWords]
    push_cast
    rfl
  · change (firstLevel L.shape.arity).eval (pub ∘ operand) s m + (6 : Word w) = ((levelStart L 0+6 : ℕ) : Word w)
    rw [eval_level h, Nat.cast_add, Nat.cast_ofNat]

/-- Executing the pair-ABI publisher writes the raw bank at workspace offset nine.
It preserves the calendar count, the controller header and all other cells. -/
theorem prepare {L B n initial phases T pub m} (h : Ready (w := w) L B n initial phases T pub m)
    (s : Word w) (a lanes : ℕ) (fit : frameBase L + 8 < 2^w) :
    let R := raw L.shape a initial phases lanes
    let M := (table L.shape a initial phases lanes).instantiate w pub
    let r := R.recipe.report (pub ∘ operand) s m
    let out := after m r.events
    execute M.program (R.recipe.code.length+1) (M.program.start s) m [] = some r ∧
      r.result = some (s+1) ∧
      Frame.data (pub 2+9) out = (fun i ↦ CursorRAM.encode w
        (inputValues n (addressBits B n) a (T*lanes) (directoryBase L) 1 (incidenceStart L 0)
          (levelStart L 0+6) i)) ∧
      (∀ addr, addr < frameBase L ∨ frameBase L+8 ≤ addr → out addr = m addr) ∧
      r.events.length = R.recipe.code.length ∧ r.probes = R.recipe.reads+8 ∧ choiceBits r.events = [] := by
  intro R M r out
  have hx : (pub 2+9).val = frameBase L := by
    change _ = L.base+9
    change L.base+9+8 < 2^w at fit
    have h9 : (9 : Word w).val = 9 := Nat.mod_eq_of_lt (by omega : 9 < 2^w)
    rw [Fin.val_add, h.workspace, h9, Nat.mod_eq_of_lt (by omega : L.base+9 < 2^w)]
  have room : (pub 2+9).val+8 ≤ 2^w := hx ▸ fit.le
  have ⟨hr,ret,store,keep,work⟩ := R.execute (pub ∘ operand) s m room
  refine ⟨(LiveStageLink.execute_widen_start ..).trans hr, ret, ?_, ?_, work⟩
  · funext j
    rw [Frame.data_at _ _ room j]
    exact (store j).trans (congrFun (raw_values h s a lanes) j)
  · intro addr ha
    apply keep addr
    change addr < (pub 2+9).val ∨ (pub 2+9).val+8 ≤ addr
    rwa [hx]

end CompressorRecords.DescriptorParameters

end VPVNP
end Computability
end OAI
