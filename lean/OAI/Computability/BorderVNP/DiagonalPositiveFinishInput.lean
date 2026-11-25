import OAI.Computability.BorderVNP.DiagonalPositiveHeaderClaims
import OAI.Computability.BorderVNP.CubePhysicalSignedClaim
import OAI.Computability.BorderVNP.DiagonalNativeSignedTags

/-! # The shared subtotal field at a genuine post-cell native state -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader.PositiveFields

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalResidueRAM DiagonalTallyRAM DiagonalTallyAllocation
open DiagonalTallyMaterialize (Operand)
open private finish_det from OAI.Computability.BorderVNP.DiagonalNativeExpansionValue
open scoped BigOperators

variable {T dim width w : ℕ}

/-- The canonical finite bit vector for the actual natural subtotal rows, in
the public team/coordinate/little-endian order. -/
def canonicalSubtotals (width : ℕ) (rows : Fin T → Fin dim → ℕ) (i : Fin (T*dim*width)) : Bool :=
  (DiagonalTallyRAM.broadcast width rows).flatten[i.val]'(i.isLt.trans_eq (flat_length rows width).symm)

theorem ofFn_canonicalSubtotals (width : ℕ) (rows : Fin T → Fin dim → ℕ) :
    List.ofFn (canonicalSubtotals width rows) = (DiagonalTallyRAM.broadcast width rows).flatten := by
  apply List.ext_getElem (List.length_ofFn.trans (flat_length rows width).symm)
  intro i hi _
  simp only [canonicalSubtotals,List.getElem_ofFn]

/-- Real state and input of the selected-ID and aligned tally suffix. The claim
bank is arbitrary. Its comparison with the local row is performed by the native
program. The operand order and counts come from the actual completed cell path. -/
structure FinishInput (t : Fin T) (rows : Fin T → Fin dim → ℕ) (width : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (state : Bank w) (mem : Memory w)
    (fields : List (List Bool)) where
  /-- The reserved output arena for this team. -/
  post : AfterTasks
  /-- Address of its copied common subtotal field. -/
  raw : ℕ
  /-- The ordered cell and cube occurrences actually supplied. -/
  operands : List Operand
  /-- Events of the selected-ID and operand producer. -/
  earlier : List (TeamRAM.Event w)
  /-- Registers at entry to the aligned allocator. -/
  bank : Bank w
  /-- Memory at entry to the aligned allocator. -/
  selected : Memory w
  prepare : Runs pub mac (.seq DiagonalTallyPacketEmit.producePacketIDs DiagonalTallyCubeSuffix.appendCubeOperands)
    state mem earlier bank selected
  allocation : AlignedAllocationInput (post.arenaFor operands.length raw dim T t.val width)
    pub selected operands fields post.descriptors
  counts : ∀ c : Fin dim, (post.arenaFor operands.length raw dim T t.val width).localRow operands c = rows t c
  capacity : operands.length ≤ post.bound.operands

variable {t : Fin T} {rows : Fin T → Fin dim → ℕ}
variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {state : Bank w} {mem : Memory w} {xs : List (List Bool)}
local notation "Finish" => finishExpansion signedOccurrences
local notation "Result" => Returns Finish pub mac state mem

/-- Every successful finish at this actual native start constrains its own
transmitted row, also on subsequent zero-valued matrix continuations. -/
theorem FinishInput.sound (h : FinishInput t rows width pub mac state mem xs) (z : Result) (c : Fin dim) :
    fieldWord w xs t c = word w (rows t c) := by
  let a := h.post.arenaFor h.operands.length h.raw dim T t.val width
  have check := signedFinish_sound a pub mac state h.bank mem h.selected h.earlier h.operands xs h.post.descriptors
    h.prepare h.allocation z.property c.val c.isLt
  rw [h.counts c,show a.team=t.val from rfl,claimWord_fieldWord a.frame (show a.dim=dim from rfl) xs t c] at check
  exact check.symm

/-- On the canonical subtotal word the linked finish really runs. Its result
retains the complete chronological unsigned trace and all serialized totals at
the fixed, count-independent address read by the residue stage. -/
theorem FinishInput.complete (h : FinishInput t rows width pub mac state mem xs)
    (canonical : xs = DiagonalTallyRAM.broadcast width rows)
    (bounded : ∀ i c, rows i c < 2^width) (sumFit : ∀ c, ∑ i, rows i c < 2^w) :
    ∃ z : Result, let a := h.post.arenaFor h.operands.length h.raw dim T t.val width
      traceCost z.val.1 ≤ traceCost h.earlier+(alignTallies.slots+allocateTallies.slots+a.work w h.operands) ∧
      (∀ e∈z.val.1,e.choices=[] ∧ e.sign=.plus ∧ e.action.extra=0) ∧
      ∀ c : Fin dim,∀ j<w, z.val.2.2 (h.post.localBase+dim+T*dim+dim+dim+1+(c.val*w+j)) =
        word w (((∑ i, rows i c).testBit j).toNat) := by
  subst xs
  let a := h.post.arenaFor h.operands.length h.raw dim T t.val width
  obtain ⟨es,z,mz,run,ticks,neutral,output⟩ := signedFinish_runs a pub mac state h.bank mem h.selected
    h.earlier h.operands h.post.descriptors (traceCost h.earlier) rows h.prepare le_rfl h.allocation h.counts bounded sumFit
  refine ⟨⟨(es,z,mz),run⟩,ticks,neutral,?_⟩
  intro c j hj
  exact (h.post.fixed_outputs h.capacity h.raw dim T t.val width w).2.2.2 ▸ output c j hj

/-- All true finish returns of a fixed post-cell state coincide, down to the
complete event sequence, registers and shared output memory. -/
theorem finish_eq (x y : Result) : x=y := by
  obtain ⟨trace,reg,ram⟩ := x.property.unique_of_deterministic
    (finish_det signedOccurrences signedOccurrences_deterministic) y.property
  exact Subtype.ext (Prod.ext trace (Prod.ext reg ram))

end TeamContraction.JointHeader.PositiveFields

end BorderVNP
end Computability
end OAI
