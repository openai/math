import OAI.Hierarchy.TaggedWideCalendarPinGeometry
import OAI.Hierarchy.TaggedWidePassiveRows

namespace OAI
/-! # Dated control words and actual state reads evaluate the retained party circuits -/

noncomputable section
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Hierarchy.WireTelescope.PassMatrix
open ThreeFlat Routing Diagonal TraceWords
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Tagged Tagged.WideControlJoin Tagged.WideStack Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ProtocolRAM.Calendar WideCPU
open scoped Classical BigOperators
private abbrev portWidth {S : ℕ} (g : Widths S) (s : Fin S) (p : (portGraph S).Port s) :=
  g p.val.1

private abbrev digitValue {Ex Sel D : Type} (G : Gate) (out : Memory G.W)
    (ext : Ex → Bool) (sel : Sel → Bool) (data : D → Bool) : SitePins Ex Sel D G → Bool :=
  Sum.elim ext (Sum.elim sel (Sum.elim data (G.terminal out)))

private abbrev fieldValue {T deg : ℕ} (P : Dated T) (work : ℕ) (j : Fin T) (s : Fin P.sites)
    {W : ℕ} (out : Memory W) (f : SiteControls.Field deg) : ℕ :=
  (out (controlAddress P work j s f)).val

/-- The three native comparison fields and the two dated history words give
the equality test on the unaffected part of this site's state. -/
theorem passiveNet_value {F Ex Sel D : Type} [Field F] [Fintype Ex] [Fintype Sel] [Fintype D]
    (G : Gate) {T deg width : ℕ} (P : Dated T) (work : ℕ) (j : Fin T) (s : Fin P.sites)
    (out : Memory G.W) (ext : Ex → Bool) (sel : Sel → Bool) (data : D → Bool)
    (dense : ∀i : Fin G.u, (G.addr i).val = i.val)
    (inside : ∀f : SiteControls.Field deg, controlAddress P work j s f < G.u)
    (rest before after : Widths P.sites) (x : State (rest+before) s) (y : State (rest+after) s)
    (l : PassiveWindow.Parts ((portGraph P.sites).Port s) (Fin deg) width
      (fun p => portWidth rest s p + portWidth before s p))
    (r : PassiveWindow.Parts ((portGraph P.sites).Port s) (Fin deg) width
      (fun p => portWidth rest s p + portWidth after s p))
    (words : Bool → Fin deg → Fin width → SitePins Ex Sel D G ⊕ Bool)
    (source : ∀i p, l.owner i = some p → ∀u : Fin (l.width i),
      Sum.elim (digitValue G out ext sel data) id (words false i (u.castLE (l.within i))) =
        (x p).val.testBit (l.base i+u.val))
    (target : ∀i p, r.owner i = some p → ∀u : Fin (r.width i),
      Sum.elim (digitValue G out ext sel data) id (words true i (u.castLE (r.within i))) =
        (y p).val.testBit (r.base i+u.val))
    (lengthRead : ∀i q, fieldValue P work j s out (.inr ((i,q),0)) =
      (PassiveWindow.header width (l.view (portWidth before s) i) (r.view (portWidth after s) q)
        (PassiveWindow.linked (portWidth rest s) (portWidth before s) (portWidth after s) l r i q)).val)
    (startRead : ∀i q (side : Bool),
      fieldValue P work j s out (.inr ((i,q),if side then 2 else 1)) =
        (PassiveWindow.heads width (l.view (portWidth before s) i) (r.view (portWidth after s) q) side).val) :
    TypedWiring.value (P:=SitePins Ex Sel D G)
        (passiveNet (F:=F) G P work j s words) (digitValue G out ext sel data) =
      if (splitPortState rest after s y).1 = (splitPortState rest before s x).1 then 1 else 0 := by
  let v := digitValue G out ext sel data
  let raw := fun side i (b : Fin width) => Sum.elim v id (words side i b)
  unfold passiveNet
  rw [PassiveWindow.eval (F:=F) (passivePins G P work j s words)
    (portWidth rest s) (portWidth before s) (portWidth after s) l r (raw false) (raw true)
    (fun p => Nat.testBit (x p).val) (fun p => Nat.testBit (y p).val) v source target]
  · rw [PassiveWindow.passive_state s rest before after x y]
    by_cases eqn : (splitPortState rest before s x).1 = (splitPortState rest after s y).1
    · simp [eqn]
    · simp [eqn,Ne.symm eqn]
  · intro i q
    rw [passivePins_read G P work j s out ext sel data dense inside words (i,q)]
    funext k
    rcases k with b|⟨side,b|b⟩
    · change (fieldValue P work j s out (.inr ((i,q),0))).testBit b.val = _
      rw [lengthRead]
      rfl
    · change (fieldValue P work j s out (.inr ((i,q),if side then 2 else 1))).testBit b.val = _
      rw [startRead]
      rfl
    · cases side <;> rfl

end Hierarchy.WireTelescope.PassMatrix

end
end OAI
