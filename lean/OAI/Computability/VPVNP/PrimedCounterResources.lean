import OAI.Computability.VPVNP.PrimedCounterResourcesSpace
import OAI.Computability.VPVNP.PrimedCounterResourcesWork
import OAI.Computability.VPVNP.PrimedInputRAMResources
import OAI.Computability.VPVNP.PrimedCounterCursor

/-!
# Simultaneous resource bounds for the scheduled primed pair parser

For every sufficiently large length the same choice of address multiplier
works for every pair and every grammar whose dense histogram has at most
the prescribed polynomial size. The work bound includes the absolute-cursor
dispatch. The external budget includes all clear, initialize, visit and
comparison calls as well as the two input passes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Resources

open BurstRAM CursorBounds PrimedInputRAM PrimedStackRAM Filter Compression

/-- Exact absolute call count and private instruction allowance of a pair. -/
def callCount (B n states : ℕ) := 10 * processorCount B n * n + labelCount n n states

/-- Uniform per-call instruction budget, taking the larger of the assembler's address-scan
bound and the parser's word-processing bound. -/
def privateFuel (B n : ℕ) :=
  max (Opcodes.nativeFuel (addressWidth B n) + 20) (12 * CursorBounds.wordBits B n + 110)

/-- Capacity inequalities for scratch storage, parser indices, the absolute cursor and the
private instruction clock at a chosen input length and address multiplier. -/
structure Bounds (B n grammarStates scratchBase : ℕ) : Prop where
  scratch : scratchBase + PrimedInputRAM.positions n (addressWidth B n) +
      size (processorCount B n) n n (labelCount n n grammarStates) ≤ 2 ^ CursorBounds.wordBits B n
  triangle : n * n ≤ 2 ^ CursorBounds.wordBits B n
  states : grammarStates < 2 ^ CursorBounds.wordBits B n
  labels : labelCount n n grammarStates ≤ processorCount B n
  cursor : callCount B n grammarStates < 2 ^ CursorBounds.wordBits B n
  component : 2 * processorCount B n * (2*n-1) < 2 ^ (2 * addressWidth B n)
  componentWord : 2 ^ (2 * addressWidth B n) ≤ 2 ^ CursorBounds.wordBits B n
  privateWork : 6 * privateFuel B n ≤ n^10
  perCall : 15 ≤ 2 ^ roundedUp 1 4 n
  total : 15 * callCount B n grammarStates ≤ 2 ^ virtualBits B n * 2 ^ roundedUp 1 4 n

/-- The calls counted by the absolute cursor use the exact budget above. -/
theorem callCount_eq (B n states : ℕ) (hn : 0 < n) :
    Cursor.calls (2 * PrimedInputRAM.positions n (addressWidth B n)) (2 * processorCount B n)
      n (2*n-1) (labelCount n n states) = callCount B n states :=
  Cursor.calls_pair (processorCount B n) n (labelCount n n states) hn

/-- The virtual bucket budget covers every group pair, including endpoint
pairs with an empty exterior cut. The returned layout uses the live word width. -/
theorem eventually_layouts (p : UniversalMachine.Program) (a d₁ d₂ C B : ℕ)
    (hB : max (max (a+1) (a+d₂)) (max d₁ C) + 2 ≤ B) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2^(n^a-1)), ∀ states, labelCount n n states ≤ n^C →
      let L := PairedChain.lengths (n^a-1) (n^d₂) (n^d₁) i
      ∃ Q : Layout L n (addressWidth B n) (liveBucket δ n) (CursorBounds.wordBits B n),
        Q.program = p ∧ Q.scratchBase = 2^(virtualBits B n) ∧
        Header.count L + labelCount n n states ≤ Q.scratchBase ∧ Opcodes.ParameterFit Q ∧
        Bounds B n states Q.scratchBase := by
  filter_upwards [eventually_physicalLayouts p a d₁ d₂ C B hB hδ hδ', eventually_privateWork B,
    eventually_virtualBucket_ge 15, eventually_pairExternalBudget B 150, eventually_ge_atTop 5]
    with n hQ hw hK htotal hn
  intro i states hT
  obtain ⟨Q,hp,hs,hh,hparams,_,_,_⟩ := hQ i (labelCount n n states) hT
  have ht := labels_le_processors (B := B) (by omega : C ≤ B) (by omega) hT
  obtain ⟨hspace,hcursor,htri,hword⟩ := space (B := B) (by omega) (by omega) ht
  have hsize : labelCount n n states < 2 ^ CursorBounds.wordBits B n := by omega
  have hb := htotal (labelCount n n states) ht
  refine ⟨Q,hp,hs,hs ▸ hh,hparams,?_⟩
  rw [hs]
  refine ⟨hspace, by simpa only [pow_two] using htri, states_fit (by omega) hsize, ht,
    hcursor, pairLabels_lt (by omega) hn, hword, hw, hK, ?_⟩
  unfold callCount
  rw [Nat.mul_assoc 10]
  omega

end PrimedCounter.Resources

end VPVNP
end Computability
end OAI
