import OAI.Hierarchy.TaggedWideCalendarDateRead
import OAI.Hierarchy.TaggedWideCalendarDateCost

namespace OAI
/-! # The two dated physical gathers on the shared spill comparator -/

noncomputable section
set_option quotPrecheck false
set_option Elab.async false
namespace Hierarchy.WireTelescope.PassMatrix
open ThreeFlat Routing Diagonal TraceWords
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Tagged Tagged.WideControlJoin Tagged.WideStack Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ProtocolRAM.Calendar WideCPU
open scoped Classical BigOperators
private abbrev spillField {T deg W : ℕ} (P : Dated T) (work : ℕ) (j : Fin T)
    (s : Fin P.sites) (out : Memory W) (f : SiteControls.Field deg) : ℕ :=
  (out (controlAddress P work j s f)).val
private abbrev spillPinValue {Ex Sel D : Type} (G : Gate) (out : Memory G.W)
    (ext : Ex → Bool) (sel : Sel → Bool) (data : D → Bool) : SitePins Ex Sel D G → Bool :=
  Sum.elim ext (Sum.elim sel (Sum.elim data (G.terminal out)))

private def spillAfter {F Ex Sel D : Type} [Field F] [Fintype Ex] [Fintype Sel] [Fintype D]
    (G : Gate) {T deg width bits : ℕ} (P : Dated T) (work : ℕ) (j : Fin T) (s : Fin P.sites)
    (inside : ∀f : SiteControls.Field deg, controlAddress P work j s f < G.u)
    (word : Bool → Fin deg → Fin width → SitePins Ex Sel D G ⊕ Bool) (small : bits ≤ G.W+1)
    (consumer : BitNetwork F (Fintype.card ((SitePins Ex Sel D G ⊕ (Fin deg × Fin width)) ⊕ (Fin deg × Fin width)))) :
    BitNetwork F (Fintype.card (SitePins Ex Sel D G ⊕ (Fin deg × Fin width))) :=
  ChordAperture.attach (F:=F) (V:=(SitePins Ex Sel D G)⊕(Fin deg × Fin width)) (I:=Fin deg)
      (fun pair pin=>Sum.map (Sum.map Sum.inl id) id (gatherPins G P work j s true (word true) pair pin))
      (fun q (b : Fin bits)=>Sum.inl (.inr (.inr (.inr (⟨_,inside (.inl (true,.inr (.inr q)))⟩,b.castLE small))) : (SitePins Ex Sel D G)))
      consumer

/-- Two locally bound chord banks use the same date's signed native fields.
The second gather passes the first complete bank through to the comparator. -/
def spillGather {F Ex Sel D : Type} [Field F] [Fintype Ex] [Fintype Sel] [Fintype D]
    (G : Gate) {T deg width bits : ℕ} (P : Dated T) (work : ℕ) (j : Fin T) (s : Fin P.sites)
    (inside : ∀f : SiteControls.Field deg, controlAddress P work j s f < G.u)
    (word : Bool → Fin deg → Fin width → SitePins Ex Sel D G ⊕ Bool) (small : bits ≤ G.W+1)
    (consumer : BitNetwork F (Fintype.card ((SitePins Ex Sel D G ⊕ (Fin deg × Fin width)) ⊕ (Fin deg × Fin width)))) :
    BitNetwork F (Fintype.card (SitePins Ex Sel D G)) :=
  gatherProgram G P work j s false (word false) small (fun q=>inside (.inl (false,.inr (.inr q))))
    (spillAfter (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=D) G P work j s inside word small consumer)

theorem spillGather_cost {F Ex Sel D : Type} [Field F] [Fintype Ex] [Fintype Sel] [Fintype D]
    (G : Gate) {T deg width bits : ℕ} (P : Dated T) (work : ℕ) (j : Fin T) (s : Fin P.sites)
    (inside : ∀f : SiteControls.Field deg, controlAddress P work j s f < G.u)
    (word : Bool → Fin deg → Fin width → SitePins Ex Sel D G ⊕ Bool) (small : bits ≤ G.W+1)
    (consumer : BitNetwork F (Fintype.card ((SitePins Ex Sel D G ⊕ (Fin deg × Fin width)) ⊕ (Fin deg × Fin width)))) :
    let net:=spillGather (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=D) G P work j s inside word small consumer
    net.cells+net.internal≤2*(deg*width+deg*(width*(200*bits+65))+deg*deg*(2308*width*(width.log2+2)))+
      (consumer.cells+consumer.internal) := by
  dsimp only
  let later:=spillAfter (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=D) G P work j s inside word small consumer
  let overhead:=deg*width+deg*(width*(200*bits+65))+deg*deg*(2308*width*(width.log2+2))
  have first : (spillGather (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=D) G P work j s inside word small consumer).cells+
      (spillGather (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=D) G P work j s inside word small consumer).internal≤overhead+(later.cells+later.internal) := by
    unfold spillGather gatherProgram
    simpa only [Fintype.card_fin] using (ChordAperture.attach_cost (F:=F) (I:=Fin deg) (V:=(SitePins Ex Sel D G)) (width:=width) (bits:=bits) _ _ later)
  have second : later.cells+later.internal≤overhead+(consumer.cells+consumer.internal) := by
    dsimp only [later,spillAfter]
    simpa only [Fintype.card_fin] using (ChordAperture.attach_cost (F:=F) (I:=Fin deg) (V:=(SitePins Ex Sel D G)⊕(Fin deg × Fin width)) (width:=width) (bits:=bits) _ _ consumer)
  change _≤2*overhead+(consumer.cells+consumer.internal)
  omega

private abbrev slotBank {K : Type} {deg width : ℕ} {sizes : K → ℕ}
    (parts : PassiveWindow.Parts K (Fin deg) width sizes) (state : K → ℕ → Bool) :
    Fin deg × Fin width → Bool :=
  Function.uncurry (ChordAperture.canonical parts state)

theorem spillGather_value {F Ex Sel D : Type} [Field F] [Fintype Ex] [Fintype Sel] [Fintype D]
    (G : Gate) {T deg width bits : ℕ} (P : Dated T) (work : ℕ) (j : Fin T) (s : Fin P.sites)
    (out : Memory G.W) (ext : Ex → Bool) (sel : Sel → Bool) (data : D → Bool)
    (dense : ∀i : Fin G.u, (G.addr i).val = i.val)
    (inside : ∀f : SiteControls.Field deg, controlAddress P work j s f < G.u)
    (word : Bool → Fin deg → Fin width → SitePins Ex Sel D G ⊕ Bool) (small : bits ≤ G.W+1)
    (consumer : BitNetwork F (Fintype.card ((SitePins Ex Sel D G ⊕ (Fin deg × Fin width)) ⊕ (Fin deg × Fin width))))
    {K : Type} {sizes : Bool → K → ℕ} (parts : ∀b, PassiveWindow.Parts K (Fin deg) width (sizes b))
    (state : Bool → K → ℕ → Bool)
    (fits : ∀b k,sizes b k≤width) (columns : width≤2^bits)
    (room : ∀b q,ChordAperture.room (parts b) q<2^bits)
    (lengthRead : ∀b i q,spillField (deg:=deg) P work j s out (.inl (b,.inl (i,q)))=(ChordAperture.sizeAt (parts b) i q).val)
    (headRead : ∀b i endp,spillField (deg:=deg) P work j s out (.inl (b,.inr (.inl (i,endp))))=(ChordAperture.head (parts b) i endp).val)
    (roomRead : ∀b q,spillField (deg:=deg) P work j s out (.inl (b,.inr (.inr q)))=ChordAperture.room (parts b) q)
    (reads : ∀b i p,(parts b).owner i=some p→∀u:Fin ((parts b).width i),
      Sum.elim (spillPinValue G out ext sel data) id (word b i (u.castLE ((parts b).within i)))=state b p ((parts b).base i+u.val)) :
    TypedWiring.value (P:=(SitePins Ex Sel D G)) (spillGather (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=D) G P work j s inside word small consumer) (spillPinValue G out ext sel data)=
      TypedWiring.value (P:=((SitePins Ex Sel D G)⊕(Fin deg × Fin width))⊕(Fin deg × Fin width)) consumer (Sum.elim (Sum.elim (spillPinValue G out ext sel data) (slotBank (parts false) (state false))) (slotBank (parts true) (state true))) := by
  let v := spillPinValue G out ext sel data
  unfold spillGather spillAfter
  rw [gatherProgram_value G P work j s out ext sel data dense inside (parts false) false (word false)
    small _ (state false) (fits false) columns (room false) (lengthRead false) (headRead false)
    (roomRead false) (reads false)]
  apply ChordAperture.attach_value (parts true) (fits true) _ _ consumer (Sum.elim v (slotBank (parts false) (state false)))
    (state true) (fun i a=>Sum.elim v id (word true i a)) (reads true) columns (room true)
  · intro q b
    change (out (G.addr ⟨controlAddress P work j s (.inl (true,.inr (.inr q))),_⟩).val).val.testBit b.val=_
    rw [dense]
    change (spillField (deg:=deg) P work j s out (.inl (true,.inr (.inr q)))).testBit b.val = _
    rw [roomRead true q]; rfl
  · intro packed i q
    have liftRead (a : ((SitePins Ex Sel D G)⊕(Fin deg × Fin width))⊕Bool) :
        Sum.elim (Sum.elim (Sum.elim v (slotBank (parts false) (state false))) packed) id (Sum.map (Sum.map Sum.inl id) id a)=
        Sum.elim (Sum.elim v packed) id a := by rcases a with (a|a)|a <;>rfl
    funext pin
    change Sum.elim _ id (Sum.map _ id (gatherPins G P work j s true (word true) (i,q) pin))=_
    rw [liftRead]
    have peel (a : (SitePins Ex Sel D G)⊕Bool) : Sum.elim (Sum.elim v packed) id (Sum.map Sum.inl id a)=Sum.elim v id a := by cases a <;>rfl
    rcases pin with b|⟨endp,b|b⟩
    · have rd:=controlWord_read G P work j s out ext sel data dense (.inl (true,.inl (i,q))) b.val (inside _)
      change Sum.elim (Sum.elim v packed) id (Sum.map Sum.inl id (controlWord G P work j s _ b.val))=_
      rw [peel,rd]
      change (spillField (deg:=deg) P work j s out (.inl (true,.inl (i,q)))).testBit b.val = _
      rw [lengthRead true i q];rfl
    · have rd:=controlWord_read G P work j s out ext sel data dense (.inl (true,.inr (.inl (i,endp)))) b.val (inside _)
      change Sum.elim (Sum.elim v packed) id (Sum.map Sum.inl id (controlWord G P work j s _ b.val))=_
      rw [peel,rd]
      change (spillField (deg:=deg) P work j s out (.inl (true,.inr (.inl (i,endp))))).testBit b.val = _
      rw [headRead true i endp];rfl
    · cases endp
      · change Sum.elim (Sum.elim v packed) id (Sum.map Sum.inl id (word true i b))=_
        change Sum.elim (Sum.elim v packed) id (Sum.map Sum.inl id (word true i b)) = Sum.elim v id (word true i b)
        exact peel _
      · rfl



end Hierarchy.WireTelescope.PassMatrix

end

end OAI
