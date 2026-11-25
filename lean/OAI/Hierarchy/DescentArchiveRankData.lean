import OAI.Hierarchy.DescentRecipeNodeTypes
import OAI.Hierarchy.DescentBundleTerminal
import OAI.Hierarchy.ProtocolRAMPortRanks

namespace OAI
/-! # Site ordinals for the nodes and private words of a coefficient archive -/

namespace Hierarchy
open DescentKernelHistory DescentSixParty DescentBundleHistory Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section

namespace DescentKernelHistory.NodeOrder
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} (B : BitDescription W)

/-- Restriction of a global ordinal assignment to the real nodes at one site.
This is the local input used to order the terminal compiler's node/operand rows. -/
def birth {n : ℕ} (order : All B ≃ Fin n) (v : W.graph.Site) : (B.recipe v).Node ↪ ℕ :=
  ⟨fun a=>(order ⟨v,a⟩).val,fun _ _ h=>eq_of_heq (Sigma.mk.inj_iff.mp (order.injective (Fin.ext h))).2⟩
end DescentKernelHistory.NodeOrder

namespace DescentHistoryOrder
variable {U P : Type} {D : ℕ} {w : P→ℕ} (N : Network D P w) (r : SiteBits (U:=U) N)
abbrev Hidden := Σu : N.Site,(r u).Hidden

section
variable {F P : Type} [Field F] {d : ℕ} {pins : P→ℕ} {W : MarkedWorld F d P pins}
abbrev SiteRank (B : BitDescription W) := Hidden W.graph B.recipe↪ℕ
end

variable {F P : Type} [Field F] {n : ℕ} {bits : P→ℕ} {W : MarkedWorld F n P bits} (B : BitDescription W)

/-- Prefix among live private variables is taken by the terminal chart. The raw word
ordinal first ranks its actual parent variable, then the chunk number inside that parent. -/
def wordRank {p : ℕ} (rank : SiteRank B) (v : W.graph.Site) :
    Private (B.recipe v) p ↪ ℕ :=
  (ProtocolRAMPortRanks.enumerate (fun h : (B.recipe v).Hidden=>(B.recipe v).hiddenWidth h/p)
    (fun h=>rank ⟨v,h⟩) (fun _ _ eqn=>eq_of_heq (Sigma.mk.inj_iff.mp (rank.injective eqn)).2)).toEmbedding.trans Fin.valEmbedding

theorem wordRank_read {p : ℕ} (rank : SiteRank B) (v : W.graph.Site) (a : Private (B.recipe v) p) :
    wordRank B rank v a=ProtocolRAMPortRanks.«prefix» (fun h=>(B.recipe v).hiddenWidth h/p)
      (fun h=>rank ⟨v,h⟩) a.1+a.2.val := rfl


end DescentHistoryOrder

namespace DescentSixParty.Chronology
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ}

/-- A coefficient description and the dense immutable ordering of precisely
its actual scalar nodes. -/
structure Archive (W : MarkedWorld F d P bits) where
  bit : BitDescription W
  count : ℕ
  order : NodeOrder.All bit ≃ Fin count
  hiddenOrder : DescentHistoryOrder.SiteRank bit

end DescentSixParty.Chronology
end
end Hierarchy

end OAI
