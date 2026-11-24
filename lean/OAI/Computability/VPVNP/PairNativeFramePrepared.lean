import OAI.Computability.VPVNP.PairNativeFrameGroup
import OAI.Computability.VPVNP.PairTerminalShadowTransfer
import OAI.Computability.VPVNP.LiveProgramPairNominationOrder

/-! # Typed leaf operands for a native auxiliary-counter preparation -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Auxiliary
open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedCounter LiveAuxiliaryHeaders PairSimulation NativeFrame
open scoped Fin.CommRing

variable {G : Group} {i : Fin (2^(sizes G).h)} {before : Memory G.w}
    {N : Indexed G Stage.nominations before (Nominations.Nom G)} {μ : Nominations.Nom G}
    {hdr : Header (pairLengths G i) → Bool} (B : PreparedBranch G before i hdr N μ)
    (Q : PrimedInputRAM.Layout (pairLengths G i) G.g.n G.g.d G.g.H G.w) (degree : Fin G.g.n) (root : Fin (states G))

/-- The source public table receives the real auxiliary reset words,
including arbitrary nomination and two-sided exterior choices. The
histogram-target frame is needed only at the single descriptor cell,
and shadow stability is needed only inside the reserved header. -/
theorem PreparedBranch.leafOperands {p r k : ℕ} (slotDegree : ℕ) (header role : Word G.w)
    (bootMem curr : Memory G.w) {row rowWords b l cap : ℕ}
    (read : Readback curr header row rowWords (cap+2) (2^b) (2^l) (TerminalBootstrap.shadowSpan (terminalOperands G) bootMem))
    (descriptor : bootMem (histogramCell G) = B.copy.memory () (histogramCell G))
    (shadowFrame : ∀ a < span (pairLengths G i) (histLength G),
      curr ((shadow G).val+a) = B.copy.memory () ((shadow G).val+a))
    (pc : LeafImage.Label → Fin p) (reg : LeafImage.Reg ↪ Fin r) (operand : LeafImage.Pub → Fin k) (ret : Fin p)
    (M : Machine G.w p r k) (assigned : M.publicData ∘ operand =
      leafWords slotDegree (terminalOperands G) header role curr ∘ LeafGeometryLoad.slot)
    (fit : (Layout.pairWorkspace G.constants).eval G.g < 2^G.w)
    (sizeFits : G.g.n < 2^G.w) (shapeFits : max (cap+2) (max (2^b) (2^l)) < 2^G.w)
    (room : shadowBase G + span (pairLengths G i) (histLength G) ≤ 2^G.w) :
    LeafFront.Operands (LeafImage.front pc reg operand ret) M curr
      (Data.ofNomination Q degree root hdr (nominationEquiv G μ)) (fromHeader slotDegree (terminalOperands G) header curr) b l cap ∧
    M.publicData (operand .size) = (G.g.n : Word G.w) := by
  let D := Data.ofNomination Q degree root hdr (nominationEquiv G μ)
  let pub := terminalOperands G
  have heq : D.hist.length = histLength G := by
    rw [show D.hist = histogram G μ from histogram_eq Q degree root hdr μ]
    simp [histogram]
  have hs : shadowBase G < 2^G.w := by
    have hw : shadowBase G ≤ (Layout.pairWorkspace G.constants).eval G.g := by
      change shadowBase G ≤ shadowBase G+_; exact Nat.le_add_right _ _
    exact hw.trans_lt fit
  have shadowVal : (pub 3).val = shadowBase G := Nat.mod_eq_of_lt hs
  have pos : 0 < shadowBase G := by
    obtain ⟨ht,hd,hh,hg⟩ := geometry_order G; omega
  have spanVal : (TerminalBootstrap.shadowSpan pub bootMem).val = span (pairLengths G i) (histLength G) := by
    rw [B.shadowSpan_of_cell descriptor,Fin.val_natCast,Nat.mod_eq_of_lt (show span (pairLengths G i) (histLength G) < 2^G.w by omega)]
  apply read.leaf_operands slotDegree pub role pc reg operand ret M assigned D b l cap rfl rfl rfl shapeFits
  · rw [heq]; exact spanVal
  · rw [spanVal,shadowVal]; exact room
  · intro a ha
    have h := shadowFrame a (spanVal ▸ ha)
    exact congrArg Fin.val (h.trans (shadow_initial Q degree root hdr μ B a))
  · exact Nat.mod_eq_of_lt sizeFits

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI
