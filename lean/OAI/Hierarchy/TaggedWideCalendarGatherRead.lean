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
private abbrev gatherValuation {Ex Sel D : Type} (G : Gate) (out : Memory G.W)
    (ext : Ex → Bool) (sel : Sel → Bool) (data : D → Bool) : SitePins Ex Sel D G → Bool :=
  Sum.elim ext (Sum.elim sel (Sum.elim data (G.terminal out)))

private abbrev gatherField {T deg W : ℕ} (P : Dated T) (work : ℕ) (j : Fin T) (s : Fin P.sites)
    (out : Memory W) (f : SiteControls.Field deg) : ℕ :=
  (out (controlAddress P work j s f)).val

/-- The finite hidden packed bank is uniquely determined by the paid width,
edge rank and cumulative prefix of that dated CPU snapshot. -/
theorem gatherProgram_value {F Ex Sel D : Type} [Field F] [Fintype Ex] [Fintype Sel] [Fintype D]
    (G : Gate) {T deg width bits : ℕ} (P : Dated T) (work : ℕ) (j : Fin T) (s : Fin P.sites)
    (out : Memory G.W) (ext : Ex→Bool) (sel : Sel→Bool) (data : D→Bool)
    (dense : ∀i : Fin G.u, (G.addr i).val = i.val)
    (inside : ∀f : SiteControls.Field deg, controlAddress P work j s f < G.u)
    {K : Type} {t : K → ℕ} (o : PassiveWindow.Parts K (Fin deg) width t)
    (side : Bool) (words₁ : Fin deg → Fin width → SitePins Ex Sel D G ⊕ Bool) (bitRoom : bits ≤ G.W+1)
    (consumer : BitNetwork F (Fintype.card (SitePins Ex Sel D G ⊕ (Fin deg × Fin width))))
    (state : K → ℕ → Bool)
    (fits : ∀p,t p≤width) (columns : width≤2^bits)
    (roomFit : ∀q,ChordAperture.room o q<2^bits)
    (lengthRead : ∀i q,gatherField (deg:=deg) P work j s out (.inl (side,.inl (i,q)))=(ChordAperture.sizeAt o i q).val)
    (headRead : ∀i b,gatherField (deg:=deg) P work j s out (.inl (side,.inr (.inl (i,b))))=(ChordAperture.head o i b).val)
    (roomRead : ∀q,gatherField (deg:=deg) P work j s out (.inl (side,.inr (.inr q)))=ChordAperture.room o q)
    (prior : ∀i p,o.owner i=some p→∀u:Fin (o.width i),
      Sum.elim (gatherValuation G out ext sel data) id (words₁ i (u.castLE (o.within i)))=state p (o.base i+u.val)) :
    TypedWiring.value (P:=SitePins Ex Sel D G) (gatherProgram (Ex:=Ex) (Sel:=Sel) (D:=D) (F:=F) G P work j s side words₁ bitRoom
        (fun q=>inside (.inl (side,.inr (.inr q)))) consumer) (gatherValuation G out ext sel data)=
      TypedWiring.value (P:=SitePins Ex Sel D G⊕(Fin deg×Fin width)) consumer (Sum.elim (gatherValuation G out ext sel data) (Function.uncurry (ChordAperture.canonical o state))) := by
  let v := gatherValuation G out ext sel data
  let src := fun i (b : Fin width) => Sum.elim v id (words₁ i b)
  unfold gatherProgram
  apply ChordAperture.attach_value o fits _ _ consumer v state (fun i=>src i) prior columns roomFit
  · intro q b
    change (out (G.addr ⟨controlAddress P work j s (.inl (side,.inr (.inr q))),_⟩).val).val.testBit b.val=_
    rw [dense]
    change (gatherField (deg:=deg) P work j s out (.inl (side,.inr (.inr q)))).testBit b.val = _
    rw [roomRead]; rfl
  · intro packed i q
    funext pin
    rcases pin with b|⟨target,b|b⟩
    · have wire:=controlWord_read G P work j s out ext sel data dense (.inl (side,.inl (i,q))) b.val (inside _)
      have peel (a : SitePins Ex Sel D G ⊕ Bool) : Sum.elim (Sum.elim v packed) id (Sum.map Sum.inl id a)=Sum.elim v id a := by cases a <;>rfl
      change Sum.elim (Sum.elim v packed) id (Sum.map Sum.inl id (controlWord G P work j s _ b.val))=_
      rw [peel,wire]
      change (gatherField (deg:=deg) P work j s out (.inl (side,.inl (i,q)))).testBit b.val = _
      rw [lengthRead]; rfl
    · have wire:=controlWord_read G P work j s out ext sel data dense (.inl (side,.inr (.inl (i,target)))) b.val (inside _)
      have peel (a : SitePins Ex Sel D G ⊕ Bool) : Sum.elim (Sum.elim v packed) id (Sum.map Sum.inl id a)=Sum.elim v id a := by cases a <;>rfl
      change Sum.elim (Sum.elim v packed) id (Sum.map Sum.inl id (controlWord G P work j s _ b.val))=_
      rw [peel,wire]
      change (gatherField (deg:=deg) P work j s out (.inl (side,.inr (.inl (i,target))))).testBit b.val = _
      rw [headRead]; rfl
    · cases target
      · change Sum.elim (Sum.elim v packed) id (Sum.map Sum.inl id (words₁ i b)) =
          Sum.elim v id (words₁ i b)
        cases words₁ i b <;> rfl
      · rfl



end Hierarchy.WireTelescope.PassMatrix

end
end OAI
