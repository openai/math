import OAI.Computability.VPVNP.LiveProgramPairAreas
import OAI.Computability.VPVNP.LiveProgramPairInitialize
import OAI.Computability.VPVNP.LiveProgramPairCopy
import OAI.Computability.VPVNP.LiveHeaderAuxiliaryStored
import OAI.Computability.VPVNP.LiveProgramPair

/-!
# The concrete native preparation of every first-half pair

Starting with the recovered live header, the nominated production words
stay in the live counter array. The initializer builds the descriptors and
the copy stage prepares every auxiliary header address in the shadow.
Unused shadow words have zero default. Header words below the descriptor
table and counters below the shadow are preserved.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Auxiliary

open BurstRAM BurstRAM.PrivateRAM LiveAuxiliaryHeaders PrimedInputRAM LiveStageLink
open ChainAssignments CutSchedule ExponentTrace
open scoped Fin.CommRing Classical

variable {G : Group} {m : Memory G.w} {i : Fin (2^(sizes G).h)}

/-- The packed histogram installed at the auxiliary machine's header addresses. -/
def histogram (G : Group) (μ : Nominations.Nom G) : List (BurstRAM.Word G.w) :=
  List.ofFn fun j => Fin.ofNat _ (μ j).val

/-- Certificate of auxiliary initialization and copying after a particular nomination,
including exact shadow contents, preserved header and counters, and bounds on native
reports and probes. -/
structure PreparedBranch (G : Group) (m : Memory G.w) (i : Fin (2^(sizes G).h))
    (hdr : Header (pairLengths G i) → Bool) (N : Indexed G Stage.nominations m (Nominations.Nom G))
    (μ : Nominations.Nom G) where
  /-- Unit-indexed initializer starting from the memory reached by the chosen nomination. -/
  init : Indexed G Stage.auxiliaryInit (N.memory μ) Unit
  /-- Unit-indexed sparse copy starting from the initializer’s final memory. -/
  copy : Indexed G Stage.auxiliaryCopy (init.memory ()) Unit
  initInputs : InputArrays (pairLengths G i) hdr (histogram G μ) (source G) (N.memory μ)
  copyPrepared : Prepared (desc G) (shadow G).val (pairLengths G i) hdr (histogram G μ) (source G) (init.memory ())
  shadowRead : ∀ a, copy.memory () ((shadow G).val+a) = headerMemory (pairLengths G i) hdr (histogram G μ) a
  headerFrame : ∀ a, headerBase G ≤ a → a < tableBase G → copy.memory () a = m a
  counterFrame : ∀ a, counterBase G ≤ a → a < shadowBase G → copy.memory () a = N.memory μ a
  initLength : (init.logs ()).length = 1
  initProbes : ∀ r ∈ init.logs (), r.probes = 25
  copyLength : (copy.logs ()).length = populated (pairLengths G i) (histLength G)+1
  copyProbes : ∀ r ∈ copy.logs (), r.probes ≤ 14
  descriptorFrame : ∀ j f, copy.memory () (LiveHeaderCopyDispatch.address (desc G) j f).val =
    init.memory () (LiveHeaderCopyDispatch.address (desc G) j f).val

/-- All required stage classifications before the compressed pair, with the
correct memories and linked report costs. -/
theorem prepare {hw : 4 ≤ G.w} {t Z : ℕ} {advice : Bits (sizes G).advice}
    {cuts : AllCuts (sizes G).h (sizes G).delta} {mode : LiveHeader.Mode.Tag}
    (out : LiveHeaderProgram.Output (sizes G) (headerBase G) G.g.d hw advice cuts
      (halves (sizes G).h (.inl i)) mode m) (evalMode : mode ≠ .unit)
    (he : (sizes G).e = t*Z) (fit : 1+t*Z ≤ (sizes G).delta)
    (room : shadowBase G + span (pairLengths G i) (histLength G) ≤ 2^G.w)
    (hb : 2*G.g.d ≤ G.w) (hn : 5*(2*G.g.d)+15 ≤ G.clockAt Stage.nominations)
    (hi : 82 ≤ G.clockAt Stage.auxiliaryInit) (hc : 71 ≤ G.clockAt Stage.auxiliaryCopy)
    (tag : G.tagged Stage.nominations m) (μ : Nominations.Nom G) :
    let F := nominationFits G i room hb hn
    let N := Nominations.indexed G F m tag
    let ξ := exteriorOf fit (liveCutEquiv (sizes G).h (sizes G).delta cuts).1
    Nonempty (PreparedBranch G m i (PairedChain.headers advice ξ i) N μ) := by
  let F := nominationFits G i room hb hn
  let N := Nominations.indexed G F m tag
  let L := pairLengths G i
  let hist := histogram G μ
  let ξ := exteriorOf fit (liveCutEquiv (sizes G).h (sizes G).delta cuts).1
  let hdr := PairedChain.headers advice ξ i
  have hlen : hist.length = histLength G := by simp [hist,histogram]
  have geometry := geometry G i hist.length hlen (hlen ▸ room)
  obtain ⟨htag,hhead,htab,hcounters⟩ := geometry_order G
  have hp : 0 < span (pairLengths G i) (histLength G) := by simp [span,Header.count]
  have hs : shadowBase G < 2^G.w := by omega
  obtain ⟨tagVal,descVal,counterVal,shadowVal⟩ := address_values G hs
  have below : G.addr.val ≤ headerBase G := by omega
  have hcounter : LiveHeaderSchedule.limit (sizes G) (headerBase G) ≤ (counter G).val := by
    change tableBase G ≤ (counter G).val; omega
  have inputs : InputArrays L hdr hist (source G) (N.memory μ) := by
    rw [Nominations.memory_eq]
    exact out.auxiliaryStoredInputArrays i evalMode he fit (counter G) F.address hcounter μ G.addr _ below
  obtain ⟨I,ready,initFrame,initLen,initCost⟩ := initialized hlen geometry.areas inputs
    geometry.tagDesc geometry.tagSource hi (N.tagged_memory rfl μ)
  have storedZero := (out.nomination_frame (counter G) F.address hcounter μ).2
  have nomFrame (a : ℕ) (ha : a ≠ G.addr.val) :
      N.memory μ a = LiveNominations.stored (counter G) F.address μ m a := by
    rw [Nominations.memory_eq]
    exact ite_eq_right ha
  have initZero (a : ℕ) : I.memory () ((shadow G).val+a) = 0 := by
    have ht : (shadow G).val+a ≠ G.addr.val := by omega
    rw [initFrame _ ht (Or.inr (by omega)),nomFrame _ ht]
    exact storedZero _ (by change (counter G).val + histLength G ≤ _; omega)
  obtain ⟨C,cs,cf,cl,cp⟩ := copied geometry.areas ready (fun a _ => initZero a) geometry.tagShadow hc
    (I.tagged_memory rfl ())
  refine ⟨⟨I,C,inputs,ready,?_,?_,?_,initLen,initCost,hlen ▸ cl,cp,?_⟩⟩
  · intro a
    by_cases ha : a < span (pairLengths G i) hist.length
    · exact cs a ha
    · rw [cf _ (by omega) (Or.inr (by omega)),initZero,headerMemory_past_end _ _ _ (Nat.le_of_not_gt ha)]
  · intro a hlow hhigh
    have ht : a ≠ G.addr.val := by omega
    rw [cf _ ht (Or.inl (by omega)),initFrame _ ht (Or.inl (by omega)),nomFrame _ ht]
    exact LiveNominations.stored_outside _ _ _ _ _ (Or.inl (by omega))
  · intro a hlow hhigh
    have ht : a ≠ G.addr.val := by omega
    rw [cf _ ht (Or.inl (by omega)),initFrame _ ht (Or.inr (by omega))]
  · intro j f
    apply cf _ (geometry.tagDesc j f) (Or.inl ?_)
    rw [LiveAuxiliaryDescriptorInit.address_val _ geometry.areas.tableFit, descVal, shadowVal]
    have := j.isLt
    have := f.isLt
    omega

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI
