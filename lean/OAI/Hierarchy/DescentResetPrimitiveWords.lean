import OAI.Hierarchy.DescentOrdinaryPrimitiveWords

namespace OAI
/-! # Primitive scalar codes at the authentic batched reset -/
namespace Hierarchy.DescentPrimitivePalette
open DescentSixParty DescentKernelHistory DescentRotor DescentResetGates DescentCompiler DescentEpochTagKeys
open DescentResetTrunks DescentRouterBank DescentChosenRouter DescentContactTree DescentResetAttachments Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
section Installed
variable {H Q U U' : Type} [Fintype H] [Fintype Q] {B : BitDescription W}
    (read : U→List (List Bool)→F) (old : Encoding U read B) (home : W.graph.Site→H) (group : Bool→W.graph.Edge→Q)
    (flag : H→Bool) {L d' : ℕ} {w : W.graph.Edge→ℕ} (same : w=W.graph.width)
    (R : Network d' (Bool×Q) (publicWidth group w)) (legacy sorted : R.Tables F) (key : W.graph.Edge↪Fin L)
    (scalar : U'→List (List Bool)→F) (r : SiteBits (U:=U') R) (valid : ReadsBits R scalar r sorted)
    (relay : U) (relayRead : read relay=equalWord) (bank : U'→U) (bankRead : ∀x,read (bank x)=scalar x)
local notation "post" => B.installed home group flag same R legacy sorted key scalar r valid
local notation "names" => NodeOrder.installedNames B home group flag same R legacy sorted key scalar r valid
local notation "codes" => Encoding.installTo read old home group flag same R legacy sorted key scalar r valid
  relay relayRead bank bankRead

theorem Encoding.installTo_at (x : NodeOrder.All post) : (codes).atNode x=
    Sum.elim old.atNode (Sum.elim (fun _=>relay) (fun v : NodeOrder.Global r=>bank ((r v.1).tag v.2))) (names x) := by
  subst w
  rcases x with ⟨⟨f,h⟩|v,n⟩
  · cases f
    · rcases n with ⟨⟨u,hu⟩,n⟩;cases hu;rfl
    · rcases n with ⟨e,he⟩;cases he;rfl
  · rfl
end Installed

variable {q ε : ℝ} {S : AtomSchedule} {k i z D w hist n h C f g cut tail s Z p : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
variable (op : RotorSpec) (menu : Runnable F op) (b : ClosedReset cap ctl) (hp : 0<p) (whole : p∣b.reset.unit)
    (fixed : Chronology.resetSpec b=op) (a : Chronology.Archive W)
    (old : Encoding (Label G s Z op) (dictionary G op menu p) a.bit)
local notation "split" => BitDescription.granular W b.count (z*G.b) b.fit a.bit
local notation "key" => DescentOrderedReset.grains W b.count b.order
local notation "fit" => (Nat.div_mul_cancel whole).symm
local notation "m" => b.reset.unit/p
local notation "pre" => (split).batchedReset b.reset b.terminals key m p hp fit (Chronology.resetMenu b)
local notation "flag" => b.terminals.hub
local notation "group" => b.reset.placement.input
local notation "same" => funext fun e=>(b.reset.allWidths e).symm
local notation "program" => b.reset.laneRecipe key m p hp fit
local notation "valid" => b.reset.lane_valid key m p hp fit (Chronology.resetMenu b)
local notation "next" => (Chronology.resetArchive b p hp whole a).bit
local notation "actual" => Encoding.reset op menu b hp whole fixed a old

def resetOrigin : NodeOrder.All next ≃ NodeOrder.All a.bit ⊕ ((W.granular b.count (z*G.b) b.fit).graph.Edge ⊕ NodeOrder.Global program) :=
  (NodeOrder.followNames b.reblock pre).trans
    (NodeOrder.installedNames split b.terminals.home group flag same b.reset.bank b.reset.tables
      (b.reset.orderedBank key) key _ program valid)

set_option maxHeartbeats 700000 in
theorem reset_at (x : NodeOrder.All next) : (actual).atNode x=Sum.elim old.atNode
    (Sum.elim (fun _=>Sum.inr (Sum.inr (Sum.inl ())))
      (fun v : NodeOrder.Global program=>Sum.inr (Sum.inr (Sum.inr
        (resetTag op b ((actual_eq b).trans fixed) ((program v.1).tag v.2)))))) (resetOrigin b hp whole a x) := by
  unfold Encoding.reset
  erw [Encoding.follow_at]
  exact Encoding.installTo_at (dictionary G op menu p)
    (⟨old.code,old.correct⟩ : Encoding (Label G s Z op) (dictionary G op menu p) split)
    b.terminals.home group flag same b.reset.bank b.reset.tables (b.reset.orderedBank key) key
    _ program valid (Sum.inr (Sum.inr (Sum.inl ()))) rfl
    (fun t => Sum.inr (Sum.inr (Sum.inr (resetTag op b ((actual_eq b).trans fixed) t))))
    (gate_eq op b menu ((actual_eq b).trans fixed)) (NodeOrder.followNames b.reblock pre x)

theorem reset_word (x : NodeOrder.All next) :
    ((codec (G:=G) op).store ((actual).atNode x)).val=Sum.elim
      (fun i=>((codec (G:=G) op).store (old.atNode i)).val)
      (Sum.elim (fun _=>censusCount s+gadgetCount G Z)
        (fun v : NodeOrder.Global program=>censusCount s+(gadgetCount G Z+(1+
          (Fintype.equivFin _ (resetTag op b ((actual_eq b).trans fixed) ((program v.1).tag v.2))).val))))
      (resetOrigin b hp whole a x) := by
  rw [reset_at op menu b hp whole fixed a old x]
  rcases resetOrigin b hp whole a x with carried|relay|bank
  · rfl
  · simp [codec,Codec.birth,Codec.ofEquiv,finSumFinEquiv_apply_right,finSumFinEquiv_apply_left]
  · rfl

end
end Hierarchy.DescentPrimitivePalette

end OAI
