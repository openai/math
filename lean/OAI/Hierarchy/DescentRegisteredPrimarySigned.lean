import OAI.Hierarchy.DescentRetainedOriginSigned
import OAI.Hierarchy.DescentResetMiddleCalendar

namespace OAI
/-! # Original signed reset register at a retained primary -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt
open DescentParallelBase DescentResetSignedScan DescentNextSignedWindow DescentCableDonorNames
open scoped Classical BigOperators Fin.CommRing
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals

open DescentIssuedFallbackPanel DescentPaidResidentCount.Reset DescentGL DescentPlainTerminal DescentResetOppositePayload
open DescentDatedAddressBook DescentSIMDLookup
set_option quotPrecheck false
local notation "prior" => input.placement
local notation "before" => input.order.trans Fin.valEmbedding
local notation "coords" => S.resetInputDigits ctl.base ctl.radix i
local notation "oldHost" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "names" => cableNames k (groupRank ((Function.Embedding.refl (Fin (S.groupCount i))).trans Fin.valEmbedding)
  (input.vertex.trans Fin.valEmbedding))
local notation "atOld" v => Stage.home (prior) v
local notation "sub" v => subcell (c:=(T).commonDepth) coords B.frame.basis (atOld v)
local notation "highAt" v => high (B.frame.enough.trans (Nat.sub_le ..))
  (rearrange B.frame.basis (oldBlock coords (atOld v)))

/-- Widening the actual encoded signed limb into the root packet preserves all
bits purchased for the preceding stage's degree and cap. -/
theorem signed_field_room (D₀ cap n₀ k₀ ht : ℕ) :
    DescentSignedCableCodec.width D₀ cap≤ResetMiddle.fieldWidth D₀ cap n₀ k₀ ht :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))

/-- Read a signed limb at the actual inverse-GL donor. The input equality is
the numeric acquired packet row, before its root-field cast is undone. -/
theorem acquired_primary_signed {field digits oldCap oldDegree b : ℕ}
    (xs : OriginalArrays B input.valid.host field) (v : W.graph.Site)
    (donorSize : digits=2^((Z).k-(T).commonDepth)) (bound : oldCap=(prior).cap)
    (deg : oldDegree=(prior).degree) (sel : Fin digits) (atDonor : sel.val=(sub v).val)
    (reg : Fin (digits*(2*oldCap))→Cell b)
    (acquired : ∀i, (reg i).val=(((DescentSignedCableCodec.encode
      (originalCable B xs ((oldHost) (((prior).pos v).2)) (highAt v)
        ((finProdFinEquiv.symm i).1.cast donorSize)
        ((finProdFinEquiv.symm i).2.cast (congrArg (2*·) bound)))).val : Cell field)).val)
    (room : DescentSignedCableCodec.width (prior).degree (prior).cap≤field)
    (j : Fin (2*oldCap)) :
    HEq (((reg (finProdFinEquiv (sel,j))).val : Cell (DescentSignedCableCodec.width oldDegree oldCap)))
      (DescentSignedCableCodec.encode (Stage.signedPanel (prior) before S input.valid names
        (atOld v) (j.cast (congrArg (2*·) bound)))) := by
  subst oldDegree oldCap
  apply heq_of_eq
  have row:=acquired (finProdFinEquiv (sel,j))
  simp only [Equiv.symm_apply_apply,Fin.cast_refl] at row
  have loc : sel.cast donorSize=(sub v).cast
      (congrArg (fun u=>2^(u-(T).commonDepth)) B.keyWidth).symm:=Fin.ext atDonor
  have cable:=original_cable_at_primary B xs v j
  erw [old_primary_root B v] at cable
  erw [Equiv.symm_apply_apply] at cable
  erw [loc,cable] at row
  let raw:=DescentSignedCableCodec.encode (Stage.signedPanel (prior) before S input.valid names (atOld v) j)
  change (reg (finProdFinEquiv (sel,j))).val=(raw.val : Cell field).val at row
  rw [Fin.val_cast_of_lt (raw.isLt.trans_le (Nat.pow_le_pow_right (by decide) room))] at row
  change ((reg (finProdFinEquiv (sel,j))).val : Cell (DescentSignedCableCodec.width _ _))=raw
  rw [row,Fin.cast_val_eq_self]


/-- Every reported digit fits the width of a real signed cable, even when
the containing acquired packet uses a wider physical alphabet. -/
theorem acquired_primary_volume {field digits oldCap b : ℕ}
    (xs : OriginalArrays B input.valid.host field) (v : W.graph.Site)
    (donorSize : digits=2^((Z).k-(T).commonDepth)) (bound : oldCap=(prior).cap)
    (sel : Fin digits)
    (reg : Fin (digits*(2*oldCap))→Cell b)
    (acquired : ∀i, (reg i).val=(((DescentSignedCableCodec.encode
      (originalCable B xs ((oldHost) (((prior).pos v).2)) (highAt v)
        ((finProdFinEquiv.symm i).1.cast donorSize)
        ((finProdFinEquiv.symm i).2.cast (congrArg (2*·) bound)))).val : Cell field)).val)
    {readWidth : ℕ} (size : DescentSignedCableCodec.width (prior).degree (prior).cap≤readWidth)
    (j : Fin (2*oldCap)) : (reg (finProdFinEquiv (sel,j))).val<2^readWidth :=by
  rw [acquired]
  let a:=DescentSignedCableCodec.encode (originalCable B xs ((oldHost) (((prior).pos v).2))
    (highAt v) ((finProdFinEquiv.symm (finProdFinEquiv (sel,j))).1.cast donorSize)
    ((finProdFinEquiv.symm (finProdFinEquiv (sel,j))).2.cast (congrArg (2*·) bound)))
  change a.val%2^field<2^readWidth
  exact (Nat.mod_le ..).trans_lt (a.isLt.trans_le (Nat.pow_le_pow_right (by decide:0<2) size))

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
