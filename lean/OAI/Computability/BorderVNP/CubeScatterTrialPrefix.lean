import OAI.Computability.BorderVNP.CubeScatterPacketStreams

/-! # Resident slices before and at a physical row trial -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open VPVNP.BurstRAM

/-- The data emitted by the first `k` trials, including the empty contributions
of rejected candidates. -/
def trialPrefix {α : Type*} {N : ℕ} (emit : Fin N → List α) (k : ℕ) : List α :=
  ((List.finRange N).take k).flatMap emit

/-- Including one more finite trial appends its whole local contribution. -/
theorem trialPrefix_step {α : Type*} {N : ℕ} (emit : Fin N → List α) (t : Fin N) :
    trialPrefix emit (t.val+1) = trialPrefix emit t.val ++ emit t := by
  simp only [trialPrefix,List.take_succ_eq_append_getElem (i := t.val) (l := List.finRange N) (by simp),
    List.getElem_finRange,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rfl

/-- At the final counter the prefix contains the complete ordered stream. -/
theorem trialPrefix_full {α : Type*} {N : ℕ} (emit : Fin N → List α) :
    trialPrefix emit N = (List.finRange N).flatMap emit := by
  rw [trialPrefix,List.take_of_length_le (by simp)]

/-- The exact split at the native trial, with rejected trials contributing an empty list. -/
theorem trialPrefix_split {α : Type*} {N : ℕ} (emit : Fin N → List α) (t : Fin N) :
    (List.finRange N).flatMap emit = trialPrefix emit t.val ++ emit t ++ ((List.finRange N).drop (t.val+1)).flatMap emit := by
  rw [← trialPrefix_step,trialPrefix,← List.flatMap_append,List.take_append_drop]

/-- Bits at their concrete shared-memory addresses, with all reads inside the
protected source region and representable in the actual word width. -/
structure Resident {w : ℕ} (src : Set ℕ) (m : Memory w) (base : ℕ) (xs : List Bool) : Prop where
  bits : BitsAt m base xs
  addresses : ∀ j < xs.length, base+j ∈ src ∧ base+j < 2^w

/-- The empty interval needs no memory reads. -/
theorem Resident.nil {w : ℕ} (src : Set ℕ) (m : Memory w) (base : ℕ) : Resident src m base [] :=
  ⟨fun j => Fin.elim0 j,fun _ h => (Nat.not_lt_zero _ h).elim⟩

/-- A constituent interval retains both its actual bits and the address bounds. -/
theorem Resident.slice {w : ℕ} {src : Set ℕ} {m : Memory w} {base : ℕ} (pre own post : List Bool)
    (h : Resident src m base (pre++own++post)) : Resident src m (base+pre.length) own := by
  refine ⟨BitsAt.slice pre own post h.bits,?_⟩
  intro j hj
  simpa only [Nat.add_assoc] using h.addresses (pre.length+j) (by simp; omega)

/-- Protected source words remain resident in every memory agreeing there. -/
theorem Resident.congr {w : ℕ} {src : Set ℕ} {m mt : Memory w} {base : ℕ} {xs : List Bool}
    (h : Resident src m base xs) (same : ∀ j ∈ src, mt j = m j) : Resident src mt base xs :=
  ⟨fun j => (same _ (h.addresses j.val j.isLt).1).trans (h.bits j),h.addresses⟩

/-- The trial at `t` is resident precisely at the base plus the length of all preceding emitted bits. -/
theorem Resident.atTrial {w N : ℕ} {src : Set ℕ} {m : Memory w} {base : ℕ}
    (emit : Fin N → List Bool) (t : Fin N) (h : Resident src m base ((List.finRange N).flatMap emit)) :
    Resident src m (base+(trialPrefix emit t.val).length) (emit t) :=
  Resident.slice _ _ _ ((trialPrefix_split emit t) ▸ h)

end Cube.Scatter

end BorderVNP
end Computability
end OAI
