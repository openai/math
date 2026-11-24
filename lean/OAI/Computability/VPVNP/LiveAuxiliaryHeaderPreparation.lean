import OAI.Computability.VPVNP.LiveAuxiliaryHeaderInputs
import OAI.Computability.VPVNP.LiveAuxiliaryDescriptorInit
import OAI.Computability.VPVNP.LiveOneShot

/-!
# Preparing a live group's sparse auxiliary RAM header

One native call reads the two exterior lengths and constructs the seven
descriptors. A sequence of native copy calls then writes the header the
auxiliary pair computation will see. The initialization phase has an accepting
exit, allowing the enclosing live stage linker to start the copy cursor at zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveAuxiliaryHeaders

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- Normal acceptance after the twenty-one descriptor words have been written. -/
def initTable := LiveOneShot.oneShot (template LiveAuxiliaryDescriptorInit.ops 27)

/-- The length-array base is the first of the seven source bases. -/
def initData (L : Lengths) (labels : ℕ) (shadow table : Word w) (src : Fin 7 → Word w) :=
  LiveAuxiliaryDescriptorInit.data L labels shadow table (src 0) src

/-- Physical address bounds used by the two stages. Table words, source words
and auxiliary destinations can be placed in distinct live scratch regions. -/
structure Areas (table shadow : Word w) (L : Lengths) (N : ℕ) (src : Fin 7 → Word w) : Prop where
  tableFit : table.val + 21 ≤ 2^w
  shadowFit : shadow.val + span L N ≤ 2^w
  countFit : populated L N < 2^w
  sourcesTable : ∀ i, (sourceAddress L N src i).val < table.val ∨ table.val + 21 ≤ (sourceAddress L N src i).val
  tableShadow : table.val + 21 ≤ shadow.val ∨ shadow.val + span L N ≤ table.val
  separated : Separated table shadow.val L N src shadowFit

/-- Both stages execute on the original live memory, including the true label
nominations. Every virtual address in the reserved zero-initialized region
returns the exact word of the §11 auxiliary header. -/
theorem prepare_native (L : Lengths) (hdr : Header L → Bool) (hist : List (Word w))
    (src : Fin 7 → Word w) (table shadow : Word w) (m : Memory w)
    (areas : Areas table shadow L hist.length src) (inputs : InputArrays L hdr hist src m)
    (fresh : ∀ a < span L hist.length, m (shadow.val+a) = 0) :
    let init := (initTable.instantiate w (initData L hist.length shadow table src)).program
    let copy := LiveHeaderCopyDispatch.program table
    let n := populated L hist.length
    ∃ es rs, execute init 79 (init.start 0) m [] = some ⟨es, none⟩ ∧
      runSegment copy 64 (some 0) (after m es) (List.replicate n []) = some rs ∧
      endState (some 0) rs = some (n : Word w) ∧ rs.length = n ∧
      (∀ a < span L hist.length,
        after (after m es) (eventLog rs) (shadow.val + a) = headerMemory L hdr hist a) ∧
      (∀ a, (a < table.val ∨ table.val+21 ≤ a) → (a < shadow.val ∨ shadow.val+span L hist.length ≤ a) →
        after (after m es) (eventLog rs) a = m a) ∧
      es.length = 78 ∧ countProbes es = 23 ∧ choiceBits es = [] ∧
      ∀ r ∈ rs, r.events.length < 64 ∧ countProbes r.events ≤ 11 ∧ choiceBits r.events = [] := by
  have hleft : m (src 0).val = (L.leftCut : Word w) := by
    simpa [cutLength] using inputs.lengths 0
  have hright : m (src 0 + 2).val = (L.rightCut : Word w) := by
    simpa [cutLength] using inputs.lengths 2
  obtain ⟨es, he, tableReady, preserved, hl, hp, hc⟩ := LiveAuxiliaryDescriptorInit.init_native
    L hist.length shadow table (src 0) src 0 m areas.tableFit hleft hright
  have hprep : Prepared table shadow.val L hdr hist src (after m es) := by
    refine ⟨tableReady, fun i => ?_⟩
    rw [preserved _ (areas.sourcesTable i)]
    exact inputs.read i
  obtain ⟨rs, hr, hstate, hm, hlen, hcost⟩ :=
    sweep_native areas.shadowFit areas.countFit areas.separated hprep
  refine ⟨es, rs, ?_, hr, hstate, hlen, ?_, ?_, hl, hp, hc, hcost⟩
  · change execute ((LiveOneShot.oneShot (template LiveAuxiliaryDescriptorInit.ops 27)).instantiate w
      (initData L hist.length shadow table src)).program 79
      ((LiveAuxiliaryDescriptorInit.program L hist.length shadow table (src 0) src).start 0) m [] = _
    rw [LiveOneShot.execute_oneShot]
    change Option.map (fun t : Report w => (⟨t.events, none⟩ : Report w)) (execute (LiveAuxiliaryDescriptorInit.program L hist.length shadow table (src 0) src) 79 _ m []) = _
    rw [he]
    rfl
  · intro a ha
    rw [hm]
    apply install_read
    rw [preserved _ (by rcases areas.tableShadow with h | h <;> omega)]
    exact fresh a ha
  · intro a ht hs
    rw [hm, install_outside _ _ _ _ _ _ _ hs, preserved _ ht]

end LiveAuxiliaryHeaders

end VPVNP
end Computability
end OAI
