import OAI.Computability.VPVNP.RAMTapeSortReplaySlot
import OAI.Computability.VPVNP.RAMTapeSortScheduleFields
import OAI.Computability.VPVNP.RAMTapeBoundaryDecision

/-! # Physical exchange fields as streams of five-word sorting records -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortReplay

open RAMSort RAMLayout RAMBoundary Boundary

variable {h d H w : ℕ}

/-- Decoding one addressed record and writing its five words recovers its original bits,
including for malformed tags and noncanonical payloads. -/
theorem recordBytes_fieldWords (w : ℕ) (raw : ℕ → Bool) (s : Stage (h+d)) (dir : Fin 2)
    (i : Fin (2^h)) :
    recordBytes (fieldWords w raw s dir i) = List.ofFn fun bit : Fin (5*w) =>
      raw ((fieldStart h w s.phase s.stride dir.val i.val).eval+bit.val) :=
  (SuccessorFields.raw_eq_flatten_words _).symm

/-- Row-major concatenation of the addressed five-word records exactly recovers the
incident send or receive field selected by this cross-site stride. -/
theorem fieldWords_bits (hslots : 2^h = 4*H) (incident : Fin (width d H w) → Bool)
    (raw : ℕ → Bool) (hraw : ∀ k : Fin (width d H w), raw k.val = incident k)
    (s : Stage (h+d)) (hc : h ≤ s.stride) (dir : Fin 2) :
    (List.ofFn fun j : Fin (blockBits H w) =>
      incident (offset d H w (.inr ((crossStageEquiv h d).symm ⟨s,hc⟩,dir,j)))) =
      blockBytes (List.ofFn (fieldWords w raw s dir)) := by
  let l := (crossStageEquiv h d).symm ⟨s,hc⟩
  let f (k : Fin (blockBits H w)) := incident (offset d H w (.inr (l,dir,k)))
  have hwidth : 2^h*(5*w) = blockBits H w := by rw [hslots, blockBits]; ring
  let f' (k : Fin (2^h*(5*w))) := f (k.cast hwidth)
  have he : List.ofFn f = List.ofFn f' := by
    apply List.ext_getElem (by simp [hwidth])
    intro k h₁ h₂
    simp [f']
  change List.ofFn f = _
  rw [he, SuccessorFields.raw_eq_flatten, blockBytes, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  change (List.ofFn fun bit => f' (finProdFinEquiv (i,bit))) = recordBytes (fieldWords w raw s dir i)
  rw [recordBytes_fieldWords]
  apply congrArg List.ofFn
  funext bit
  rw [fieldStart_physical hslots s hc dir i bit, hraw]
  apply congrArg (fun k : Fin (blockBits H w) => incident (offset d H w (.inr (l,dir,k))))
  apply Fin.ext
  change bit.val + 5*w*i.val = i.val*5*w+bit.val
  ring

/-- The two consecutive streams in the physical schedule carry exactly the rows
of the outgoing and incoming blocks for this stage. -/
theorem fieldPair_eq_blocks (hslots : 2^h = 4*H) (incident : Fin (width d H w) → Bool)
    (raw : ℕ → Bool) (hraw : ∀ k : Fin (width d H w), raw k.val = incident k)
    (s : Stage (h+d)) (hc : h ≤ s.stride) :
    SortSchedule.fieldPair incident ((crossStageEquiv h d).symm ⟨s,hc⟩).ordinal.val =
      blockBytes (List.ofFn (fieldWords w raw s 0)) ++ blockBytes (List.ofFn (fieldWords w raw s 1)) := by
  let l := (crossStageEquiv h d).symm ⟨s,hc⟩
  rw [SortSchedule.fieldPair, dite_eq_left l.ordinal.isLt]
  change (List.ofFn fun k : Fin (blockBits H w) =>
    incident (offset d H w (.inr ((layerEquiv d).symm ((layerEquiv d) l),0,k)))) ++
    (List.ofFn fun k : Fin (blockBits H w) =>
    incident (offset d H w (.inr ((layerEquiv d).symm ((layerEquiv d) l),1,k)))) = _
  rw [Equiv.symm_apply_apply]
  exact congrArg₂ List.append (fieldWords_bits hslots incident raw hraw s hc 0)
    (fieldWords_bits hslots incident raw hraw s hc 1)

end RAMTape.SortReplay

end VPVNP
end Computability
end OAI
