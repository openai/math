import OAI.Computability.VPVNP.LiveAuxiliaryHeaderPreparation
import OAI.Computability.VPVNP.LiveCountedStage
import OAI.Computability.VPVNP.LiveHeaderBounded
import OAI.Computability.VPVNP.LiveHeaderSchedule
import OAI.Computability.VPVNP.LiveNominationSweep

/-!
# Stage tables for nomination and auxiliary header preparation

The nomination stage accepts when the cursor reaches the public production-label
count. The descriptor initializer accepts after one call. The copy stage uses the
seventh descriptor's cumulative end, read from live scratch on each call. Both
boundary checks have deterministic accepting exits on an empty choice stream.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveAuxiliaryStages

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM
open LiveHeaderCopyDispatch
open scoped Fin.CommRing

/-- Run the nomination worker under a public production-label bound, accepting at the end of
the label scan. -/
def nomination := LiveHeaderBounded.bounded (LiveNominations.flow.template (some 7))

/-- The one-call stage that creates the auxiliary header descriptor table. -/
abbrev «initialize» := LiveAuxiliaryHeaders.initTable

/-- The counted sparse-copy stage whose stopping bound is read from the last auxiliary
descriptor. -/
def copy := LiveCountedStage.counted (LiveHeaderCopyDispatch.flow.template (some 11)) true

variable {w b : ℕ}

/-- The nomination worker's public data extended with the label count used by its stage guard. -/
def nominationData (b : ℕ) (base : Word w) (count : Word w) :=
  LiveHeaderBounded.publicData (LiveNominations.data b base) count

/-- The final packed end is field zero of the seventh descriptor. -/
def copyData (table : Word w) :=
  LiveCountedStage.publicData (fun _ : Fin 1 => table) (address table 6 0)

/-- The output ranges produced by the preceding header recovery and nomination stages. -/
def headerSources (s : LiveHeaderSchedule.Sizes) (headerBase : ℕ) (muBase : Word w) : Fin 7 → Word w :=
  ![(LiveHeaderSchedule.widthAddr headerBase .primedLeft : Word w),
    (LiveHeaderSchedule.leftIndexBase s headerBase : Word w),
    (LiveHeaderSchedule.rightIndexBase s headerBase : Word w),
    (LiveHeaderSchedule.adviceBase s headerBase : Word w),
    (LiveHeaderSchedule.exteriorBase s headerBase .left : Word w),
    (LiveHeaderSchedule.exteriorBase s headerBase .right : Word w), muBase]

/-- The initializer's public input uses capacities and addresses only. The two
exterior lengths that depend on the group are read from the first source array. -/
def initializeData (index advice capacity labels : ℕ) (shadow table : Word w) (src : Fin 7 → Word w) :
    Fin 14 → Word w :=
  ![(index : Word w),(advice : Word w),(capacity : Word w),(labels : Word w),shadow,table,src 0,
    src 0,src 1,src 2,src 3,src 4,src 5,src 6]

theorem initializeData_eq (L : Lengths) (labels : ℕ) (shadow table : Word w) (src : Fin 7 → Word w) :
    initializeData L.index L.advice L.cutCapacity labels shadow table src =
      LiveAuxiliaryHeaders.initData L labels shadow table src := rfl

theorem copy_endAddress (table : Word w) : address table 6 0 = table + 18 := by rfl

/-- The component template and the cursor guard together consume the specified
bits, preserving the stored value and the one-probe bound. -/
theorem nomination_active (hb : b ≤ w) (base count state : Word w) (hs : state < count)
    (m : Memory w) (v : Word b) :
    let P := (nomination.instantiate w (nominationData b base count)).program
    ∃ es, execute P (5*b+15) (P.start state) m (wordBits v) = some ⟨es, some (state+1)⟩ ∧
      after m es = writeMemory m (base+state) (Fin.ofNat (2^w) v.val) ∧
      es.length = 5*b+14 ∧ countProbes es = 1 ∧ choiceBits es = wordBits v := by
  obtain ⟨es, he, hm, hl, hp, hc⟩ := LiveNominations.component_native hb base state m v
  refine ⟨.tick :: .tick :: .tick :: es, ?_, hm, ?_, hp, hc⟩
  · apply (LiveHeaderBounded.execute_active (LiveNominations.flow.template (some 7))
      (LiveNominations.data b base) count (5*b+12) state hs m (wordBits v)).trans
    change (execute (LiveNominations.program b base) _ ((LiveNominations.program b base).start state) _ _).map _ = _
    rw [he]; rfl
  · simp only [List.length_cons, hl]

/-- The last nomination call transfers to descriptor initialization, including
when the production-label count is zero. -/
theorem nomination_closed (b fuel : ℕ) (base count state : Word w) (hs : count ≤ state)
    (m : Memory w) (bits : List Bool) :
    let P := (nomination.instantiate w (nominationData b base count)).program
    execute P (fuel+4) (P.start state) m bits =
      if bits = [] then some ⟨[.tick,.tick,.tick], none⟩ else none :=
  LiveHeaderBounded.execute_closed _ _ count fuel state hs m bits

/-- The copy wrapper performs one extra read of the cumulative end, then the
dispatcher copies the selected word. -/
theorem copy_active (table : Word w) (ds : Fin 7 → Descriptor w) (m : Memory w)
    (ready : Spec table ds m) (state : Word w) (endFits : state < (ds 6).endOffset)
    (i : Fin 7) (hskip : ∀ j < i, (ds j).endOffset ≤ state) (hhit : state < (ds i).endOffset) :
    let P := (copy.instantiate w (copyData table)).program
    let offset := state - prevEnd ds i
    ∃ es, execute P 68 (P.start state) m [] = some ⟨es, some (state+1)⟩ ∧
      after m es = writeMemory m ((ds i).targetBase + offset) (m ((ds i).sourceBase + offset).val) ∧
      es.length < 68 ∧ countProbes es ≤ 12 ∧ choiceBits es = [] := by
  let addr := address table 6 0
  have ha : state < LiveCountedStage.limit true addr m := by
    change state < m (address table 6 0).val
    rw [ready.ends]
    exact endFits
  obtain ⟨es, he, hm, hl, hp, hc⟩ := row_native table ds state m ready i hskip hhit
  refine ⟨LiveCountedStage.guardEvents true addr m ++ es, ?_, hm, ?_, ?_, hc⟩
  · apply (LiveCountedStage.execute_active (LiveHeaderCopyDispatch.flow.template (some 11))
      true (fun _ => table) addr 64 state m ha []).trans
    change (execute (LiveHeaderCopyDispatch.program table) _ ((LiveHeaderCopyDispatch.program table).start state) _ _).map _ = _
    rw [he]; rfl
  · simp [LiveCountedStage.guardEvents]; omega
  · change 1 + countProbes es ≤ 12
    omega

/-- The cursor at the end of the populated header accepts without touching
the sparse virtual destinations. -/
theorem copy_closed (table : Word w) (ds : Fin 7 → Descriptor w) (m : Memory w)
    (ready : Spec table ds m) (fuel : ℕ) (state : Word w) (hs : (ds 6).endOffset ≤ state)
    (bits : List Bool) :
    let P := (copy.instantiate w (copyData table)).program
    execute P (fuel+5) (P.start state) m bits =
      if bits = [] then some ⟨LiveCountedStage.guardEvents true (address table 6 0) m, none⟩ else none :=
  LiveCountedStage.execute_closed _ true _ (address table 6 0) fuel state m
    (by change m (address table 6 0).val ≤ state; rw [ready.ends]; exact hs) bits

end LiveAuxiliaryStages

end VPVNP
end Computability
end OAI
