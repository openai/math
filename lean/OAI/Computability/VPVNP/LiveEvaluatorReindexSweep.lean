import OAI.Computability.VPVNP.LiveEvaluatorReindexImage
import OAI.Computability.VPVNP.LiveEvaluatorReindexNative

/-!
# Native permutation of all dense exponent bits

The incoming scratch stores one binary digit per word. The decoded order
table names its formal row. Every native scatter reads exactly these two
words, computes the reversed tagged payload position, and writes one tape
symbol. Its last burst accepts, including the empty permutation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorReindex

open BurstRAM BurstRAM.PrivateRAM RAMSerialization EvaluatorProgramRawInput
open scoped Fin.CommRing

variable {d t Z w : ℕ}

/-- Length parameters and disjoint intervals used by the native scan. -/
structure Layout (pub : Fin 5 → Word w) (d t Z stateBase M A : ℕ) : Prop where
  width : (pub 3).val = Z
  total : (pub 4).val = t*Z
  target : (pub 2).val = stateBase + 1 + M + A + (2*Z+1) + 1
  sourceFit : (pub 0).val + d*Z ≤ 2^w
  mapFit : (pub 1).val + d ≤ 2^w
  targetFit : (pub 2).val + 2*(t*Z) ≤ 2^w
  sourceDisjoint : (pub 0).val + d*Z ≤ (pub 2).val ∨ (pub 2).val + 2*(t*Z) ≤ (pub 0).val
  mapDisjoint : (pub 1).val + d ≤ (pub 2).val ∨ (pub 2).val + 2*(t*Z) ≤ (pub 1).val

/-- Values of the incoming digit and order-advice buffers after the live
header scan and advice unpacking stages. -/
structure Sources (pub : Fin 5 → Word w) (perm : Fin d ≃ Fin t) (dense : Fin d → Word Z)
    (m : Memory w) : Prop where
  incoming : ∀ q : Fin (d*Z), m ((pub 0).val + q.val) = PrimedInputRAM.encodeBit w (arrayBits d Z dense q)
  order : ∀ i : Fin d, (m ((pub 1).val + i.val)).val = (perm i).val

private theorem bitOrder_val (perm : Fin d ≃ Fin t) (q : Fin (d*Z)) :
    (bitOrder perm Z q).val = (perm q.divNat).val * Z + q.val % Z := by
  change q.val % Z + Z * (perm q.divNat).val = _
  ac_rfl

private theorem address_eq {pub : Fin 5 → Word w} {base M A : ℕ} (L : Layout pub d t Z base M A)
    (f : Fin (t*Z)) : symbolAddress base M A Z f = (pub 2).val + 2*(t*Z-1-f.val) := by
  rw [L.target]
  unfold symbolAddress rawSlot payload
  omega

private theorem image_step (hw : 2 ≤ w) (pub : Fin 5 → Word w) (perm : Fin d ≃ Fin t)
    (dense : Fin d → Word Z) {base M A : ℕ} (L : Layout pub d t Z base M A)
    {original m : Memory w} (src : Sources pub perm dense original) (q : Fin (d*Z))
    (h : Image perm dense base M A q.val original m) :
    Image perm dense base M A (q.val+1) original (after m (phaseEvents pub (q.val : Word w) m)) := by
  have hq : (q.val : Word w).val = q.val := Fin.val_cast_of_lt (q.isLt.trans_le ((Nat.le_add_left ..).trans L.sourceFit))
  have ha := incomingAddress_val pub (q.val : Word w) (by rw [hq]; have := q.isLt; have := L.sourceFit; omega)
  rw [hq] at ha
  have hj : q.val / Z < d := q.divNat.isLt
  have hm := mapAddress_val pub (q.val : Word w) (by rw [hq, L.width]; have := L.mapFit; omega)
  rw [hq, L.width] at hm
  have hdata : m (incomingAddress pub (q.val : Word w)).val =
      PrimedInputRAM.encodeBit w (arrayBits d Z dense q) := by
    rw [ha, h.outside ((pub 0).val + q.val) (by
      intro s _
      rw [address_eq L]
      have := L.sourceDisjoint
      have := q.isLt
      have := (bitOrder perm Z s).isLt
      omega), src.incoming]
  have hmap : (m (mapAddress pub (q.val : Word w)).val).val = (perm q.divNat).val := by
    rw [hm, h.outside ((pub 1).val + q.val / Z) (by
      intro s _
      rw [address_eq L]
      rcases L.mapDisjoint with lo | hi
      · exact ne_of_lt ((Nat.add_lt_add_left hj _).trans_le (lo.trans (Nat.le_add_right ..)))
      · have hs := (bitOrder perm Z s).isLt
        have hback : 2*(t*Z-1-(bitOrder perm Z s).val) < 2*(t*Z) := by omega
        exact ne_of_gt ((Nat.add_lt_add_left hback _).trans_le (hi.trans (Nat.le_add_right ..))))]
    exact src.order q.divNat
  have hf : (m (mapAddress pub (q.val : Word w)).val).val * (pub 3).val +
      (q.val : Word w).val % (pub 3).val = (bitOrder perm Z q).val := by
    rw [hq, hmap, L.width, bitOrder_val]
  have hdest := targetAddress_val pub (q.val : Word w) m hw
    (by rw [hf, L.total]; exact (bitOrder perm Z q).isLt)
    (by rw [hf, L.total]; have := L.targetFit; have := (bitOrder perm Z q).isLt; omega)
  rw [hf, L.total, ← address_eq L] at hdest
  rw [after_phaseEvents, inputSymbol, hdata]
  exact h.write q _ hdest

/-- The real native phase accepts after exactly one call per input bit, or
one no-op call if the dense vector is empty. Its final bank is the exact
two-tape initial configuration expected by the formal-coordinate evaluator. -/
theorem sweep_native (hw : 2 ≤ w) (pub : Fin 5 → Word w) (perm : Fin d ≃ Fin t)
    (dense : Fin d → Word Z) (formal : Fin t → Word Z) (order : ∀ i, formal (perm i) = dense i)
    (p : UniversalMachine.Program) (running : p.extra ≠ 0) (hs : p.extra+2 ≤ 2^w)
    (A : List Bool) (base M : ℕ) (L : Layout pub d t Z base M A.length) (before : Memory w)
    (src : Sources pub perm dense before) (space : (A ++ runtime formal).length ≤ M+1)
    (prepared : LiveEvaluatorInitialize.Stores hw hs base before
      (LiveEvaluatorTail.initialCode M (UniversalMachine.initial p (A ++ runtime (fun _ : Fin t => (0 : Word Z)))))) :
    let P := (scatterPhase.instantiate w pub).program
    ∃ rs, runSegment P 27 (some 0) before (List.replicate (max 1 (d*Z)) []) = some rs ∧
      endState (some 0) rs = none ∧
      LiveEvaluatorInitialize.Stores hw hs base (after before (eventLog rs))
        (LiveEvaluatorTail.initialCode M (UniversalMachine.initial p (A ++ runtime formal))) ∧
      rs.length = max 1 (d*Z) ∧ ∀ r ∈ rs, countProbes r.events ≤ 3 := by
  have hdt : d = t := by simpa using Fintype.card_congr perm
  obtain ⟨rs, hr, halt, image, len, probes⟩ := scatterPhase_segment pub (d*Z) (by rw [hdt, L.total])
    (fun n => Image perm dense base M A.length n before) before (Image.zero ..)
    (fun j hj _ h => image_step hw pub perm dense L src ⟨j, hj⟩ h)
  exact ⟨rs, hr, halt, stores_formal p running hw hs perm dense formal order A base M space before _ prepared image,
    len, probes⟩

end LiveEvaluatorReindex

end VPVNP
end Computability
end OAI
