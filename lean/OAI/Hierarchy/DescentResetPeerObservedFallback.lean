import OAI.Hierarchy.DescentFundedRootObservation
import OAI.Hierarchy.DescentResetPeerRecordedOrigins

namespace OAI
/-! # Structural private roots from the reached signed and rank snapshot -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentGL DescentColonies DescentSIMDLookup DescentRotorRootPresence DescentResetHostSize
open DescentFallbackPeriod DescentSharedBookScan DescentIssuedFallbackPanel DescentRosterOrder
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ) (groups : J↪ℕ) (vertex : V↪Fin H)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
    (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
    (obs : RootObservation A S ready digits native groups vertex Z T frame field)
local notation "c" => T.commonDepth
local notation "r" => Z.k-c
local notation "ord" => frame.host.symm.toEmbedding.trans vertex
local notation "roots" => leafPanel A S ready digits native Z T frame
local notation "input" => fun (v : Fin H) (hi : Block T.commonDepth) => (packet (D:=A.degree) («L»:=2^(m-c)) («cap»:=A.cap) (n:=Z.n) («r»:=r)
  (field:=field) (obs.packed v hi))
local notation "ticket" => fun (t : Z.Fallback) => (Z.fallLabel T t,(T.code t).2.2)

theorem observed_live_root (s : Bool) (t : Z.Fallback) :
    key (Ht:=Ht) (l:=Z.layerBits) s (ticket t)
      (input (vertex (frame.host.symm (T.code t).1)) (Z.rootBlock T (.inr t))) =
      Z.fallbackKey T s t (roots s t) := by
  simp only [RootObservation.packed, packet_encode]
  exact received_fallback_key (A:=A) (S:=S) (ready:=ready) (digits:=digits) (native:=native)
      (Z:=Z) (T:=T) (frm:=frame) (s:=s) (t:=t) (roster:=obs.roster) (bank:=obs.chart) (source:=obs.memory)
      (target:=obs.cutoff) (word:=obs.word) (groupKey:=groups) (vertex:=vertex)
      (ownCell:=obs.stencilRead) (neighbors:=obs.rosterRead) (wireCells:=obs.markRead)
      (header:=obs.header) (safe:=obs.room) (table:=obs.layouts) (old:=obs.old) (hub:=obs.hubs)
      (ww:=obs.pos) (bitsFit:=obs.heightFits) (avail:=obs.available) (encoded:=obs.encoded)
      (allSites:=obs.allSites) (room:=obs.wordFits) (onWire:=obs.onWire)
      (signBits:=obs.signedFits) (countBits:=obs.countFits)

theorem observed_empty_root (s : Bool) (t : Code r×Option (Fin (2^Z.n))) (v : V) (hi : Block c)
    (absent : Z.atRoot T ord (vertex v,hi,.inr t)=none) :
    key (Ht:=Ht) (l:=Z.layerBits) s t (input (vertex v) hi)=none := by
  simp only [RootObservation.packed, packet_encode]
  exact received_fallback_ghost (A:=A) (S:=S) (ready:=ready) (digits:=digits) (native:=native)
      (Z:=Z) (T:=T) (frm:=frame) (s:=s) (p:=t) (v:=v) (hi:=hi) (roster:=obs.roster) (bank:=obs.chart) (source:=obs.memory)
      (word:=obs.word) (groupKey:=groups) (vertex:=vertex)
      (ownCell:=obs.stencilRead) (neighbors:=obs.rosterRead) (wireCells:=obs.markRead)
      (allSites:=obs.allSites) (room:=obs.wordFits) (absent:=absent)

end
end Hierarchy.DescentSixParty.GroupStage

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames
open DescentCompiler DescentColonies DescentGL DescentFallbackPeriod DescentSIMDLookup DescentResetHostSize
open DescentPaidResidentCount.Reset
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z w hist D n h C f g cut tail H a : ℕ}
    {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl) (pad : Fintype.card input.V ≤ H)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "r" => (Z).k-cc
local notation "depth" => GroupStage.depthBound D n f g
local notation "L" => 2^(S.groupWidth k tail i+k-cc)
local notation "cap" => input.placement.cap
local notation "D₀" => input.placement.degree
local notation "vertex" => input.vertex.trans (Fin.castLEEmb pad)
local notation "tall" => B.frame.host.symm.toEmbedding.trans vertex
local notation "arr" => privatePanelAt B (private_count_eq B)
variable (snap : PaddedSnapshot B pad a)
local notation "older" => fun (v : Fin H) (hi : Block cc) => packet (D:=D₀) («L»:=L) («cap»:=cap) (n:=(Z).n) («r»:=r) (field:=a) (snap.packed v hi)
local notation "word" => fun (v : Fin H) (hi : Block cc) => packet (D:=D₀) («L»:=2^r) («cap»:=cap) (n:=(Z).n) («r»:=r) (field:=a) (savedInput B pad snap v hi)
local notation "tag" => fun (t : (Z).Fallback) => ((Z).fallLabel T t,((T).code t).2.2)

private theorem prior_root_keys :
    (∀s t,key (Ht:=depth) (l:=(Z).layerBits) s (tag t)
      (older (tall ((Z).rootVertex T (.inr t))) ((Z).rootBlock T (.inr t)))=
      (Z).fallbackKey T s t (privatePanelCatalog B s t)) ∧
    ∀s t v hi,(Z).atRoot T tall (tall v,hi,.inr t)=none →
      key (Ht:=depth) (l:=(Z).layerBits) s t (older (tall v) hi)=none := by
  rcases input with @⟨V,vFin,vDec,phase,ready,rfl,rfl,history,degree,order,ord,edgeName,siteName⟩
  rcases B with ⟨ct,rfl,oldFit,source,orderEq,R,T₀,age,date,extent,tickets,unit,dimension,
    tapeWidth,graph,fr,roster,raw,rawGeometry,rawHub,rawValid,grain,wire,atoms,branch,capacity⟩
  subst source
  let dig:=S.resetInputDigits ctl.base ctl.radix i
  let oldId:=ord.trans (Fin.castLEEmb pad)
  let gId:=Fin.valEmbedding (n:=S.groupCount i)
  constructor
  · exact fun s t=>GroupStage.observed_live_root phase S ready dig (order.trans Fin.valEmbedding) gId oldId R T₀ fr snap s t
  · intro s t v hi missing
    exact GroupStage.observed_empty_root phase S ready dig (order.trans Fin.valEmbedding) gId oldId R T₀ fr snap s t
      (fr.host.symm v) hi missing

/-- Changing the number of leaf slots along the actual key-width equality preserves
the live and empty private root answers, including every recorded leaf on each side. -/
theorem peer_fallback_roots :
    (∀s t,key (Ht:=depth) (l:=(Z).layerBits) s (tag t)
      (word (tall ((Z).rootVertex T (.inr t))) ((Z).rootBlock T (.inr t)))=
      (Z).fallbackKey T s t (arr s t)) ∧
    ∀s t v hi,(Z).atRoot T tall (tall v,hi,.inr t)=none →
      key (Ht:=depth) (l:=(Z).layerBits) s t (word (tall v) hi)=none := by
  have ⟨live,empty⟩:=prior_root_keys B pad snap
  have eqn : L=2^r:=by rw [B.keyWidth]
  let out (l : ℕ) (h₀ : L=l) (v : Fin H) (hi : Block cc) :=
    Fin.cast (congrArg (fun slots=>2^(a*inputCount D₀ slots cap (Z).n r)) h₀) (snap.packed v hi)
  have both (l : ℕ) (h₀ : L=l) :
      (∀s t,key (Ht:=depth) (l:=(Z).layerBits) s (tag t)
        (packet (D:=D₀) («L»:=l) («cap»:=cap) (n:=(Z).n) («r»:=r) (field:=a)
          (out l h₀ (tall ((Z).rootVertex T (.inr t))) ((Z).rootBlock T (.inr t))))=
        (Z).fallbackKey T s t (privatePanelAt B (congrArg (fun slots=>slots*(2*cap)) h₀) s t)) ∧
      ∀s t v hi,(Z).atRoot T tall (tall v,hi,.inr t)=none →
        key (Ht:=depth) (l:=(Z).layerBits) s t
          (packet (D:=D₀) («L»:=l) («cap»:=cap) (n:=(Z).n) («r»:=r) (field:=a) (out l h₀ (tall v) hi))=none := by
    subst l; exact ⟨live,empty⟩
  exact both _ eqn

/-- The scored input can be reconstructed from the measured signed and rank
arrays on the public residual dimension. The transport only changes finite indices. -/
theorem observed_packet {slots : ℕ} (eqn : L=slots)
    (shape : Fin H→Block cc→Fin slots→ℕ)
    (cables : Fin H→Block cc→Fin slots→Fin (2*cap)→Option (DescentSharedCableNames.Stage.Live D₀ cap))
    (shapeRead : ∀v hi x,shape v hi (Fin.cast eqn x)=snap.stencil v hi x)
    (wireRead : ∀v hi x j,cables v hi (Fin.cast eqn x) j=snap.marks v hi x j)
    (v : Fin H) (hi : Block cc) :
    let rank:=fun h j=>(DescentSharedBookScan.ranks (a:=r) (Y:=2^(Z).n) (D:=D₀)
      snap.chart (2^depth) (depth+2) snap.memory h j).val
    encodePacket (inputs shape snap.peers cables rank v hi : Packet D₀ slots cap (Z).n r a)=
      Fin.cast (congrArg (fun n=>2^(a*inputCount D₀ n cap (Z).n r)) eqn) (snap.packed v hi) := by
  subst slots
  have fixedShape : shape=snap.stencil:=funext fun v=>funext fun hi=>funext fun x=>shapeRead v hi x
  have fixedCables : cables=snap.marks:=funext fun v=>funext fun hi=>funext fun x=>funext fun j=>wireRead v hi x j
  subst shape; subst cables
  rfl

theorem observed_peer_input
    (shape : Fin H→Block cc→Block r→ℕ)
    (cables : Fin H→Block cc→Block r→Fin (2*cap)→Option (DescentSharedCableNames.Stage.Live D₀ cap))
    (shapeRead : ∀v hi x,shape v hi (Fin.cast (by rw [B.keyWidth]) x)=snap.stencil v hi x)
    (wireRead : ∀v hi x j,cables v hi (Fin.cast (by rw [B.keyWidth]) x) j=snap.marks v hi x j)
    (v : Fin H) (hi : Block cc) :
    let rank:=fun h j=>(DescentSharedBookScan.ranks (a:=r) (Y:=2^(Z).n) (D:=D₀)
      snap.chart (2^depth) (depth+2) snap.memory h j).val
    (inputs shape snap.peers cables rank v hi : Packet D₀ (2^r) cap (Z).n r a)=word v hi := by
  intro rank
  dsimp only
  rw [←show encodePacket (inputs shape snap.peers cables rank v hi : Packet D₀ (2^r) cap (Z).n r a)=
      savedInput B pad snap v hi from observed_packet B pad snap (by rw [B.keyWidth])
      shape cables shapeRead wireRead v hi,packet_encode]

open DescentDenseHostOrder DescentPackedPrivateMenu DescentFallbackPeriod.Projected.Receiver
local notation "full" => input.placement.wire*(input.placement.z*G.b)*cap
local notation "digit" => fieldBits (Z).graph r depth (2^r*(2*cap)) (DescentRecordedRotorLayers.width f cap) C (Z).width
local notation "host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "slots_" => Fin L×Fin (2*cap)
local notation "actor" => (Z).sparseActor T tall
local notation "rank_" => fun h j=>(DescentSharedBookScan.ranks (a:=r) (Y:=2^(Z).n) (D:=D₀)
    snap.chart (2^depth) (depth+2) snap.memory h j).val

/-- All private record claims and all key decisions are consequences of the actual
preceding rank/signed snapshot. The stem pass supplies only its own original keys. -/
theorem snapshot_peer_origins {nbits t keyBits p : ℕ} (recorded : B.Recorded p) (μ : Layout (Z).k)
    (levels : Fin H→ℕ) (stencil : Fin H→Block cc→Block r→Cell t)
    (cables : Fin H→Block cc→Block r→Fin (2*cap)→Option (DescentSharedCableNames.Stage.Live D₀ cap))
    (unit : 0 < (Z).unit) (keys : Fin (stemsCount B)→Fin H→Block cc→Cell keyBits)
    (stem : ∀(u : host) s (j : slots_),(keys (stemAxis B (s,j)) (((Z).hostFields T tall u.1.2).1) (peerLane B u)).val=
      DescentResetStemKey.code ((oldStemAt B u s j).map (stemTicket B s)))
    (won : HEq μ B.frame.basis) (residual : r < 2^nbits) (one : 1 < 2^nbits)
    (bound : 2^r*full < 2^nbits) (fit : 2*DescentFallbackShapeTable.rows r (2^(Z).n) ≤ 2^t)
    (active : 0 < full) (quotaPositive : 0 < quota S.rounds) (degreePositive : 0 < 32*Nat.clog 2 (2*D₀))
    (levelRead : ∀v,levels (vertex v)=(Z).placement.b (B.frame.host v))
    (stamped : ∀v hi lo,stencil (vertex v) hi lo=Recorded.realPanel (reset:=B) B.keyWidth μ nbits t v hi lo)
    (precision : t ≤ a) (depthFits : r+1 < 2^a) (capFits : cap < 2^a)
    (shapeRead : ∀v hi x,(stencil v hi (Fin.cast (by rw [B.keyWidth]) x)).val=snap.stencil v hi x)
    (wireRead : ∀v hi x j,cables v hi (Fin.cast (by rw [B.keyWidth]) x) j=snap.marks v hi x j) :
    let headers:=goodInput cc a cap (Fintype.card input.V) levels (fun v hi j=>((stencil v hi j).val:Cell a))
    let packets:=fun (_:Bool) (_:Code r×Option (Fin (2^(Z).n))) v hi=>
      (inputs (fun v hi j=>(stencil v hi j).val) snap.peers cables rank_ v hi : Packet D₀ (2^r) cap (Z).n r a)
    let values:=privatePageValue (Ht:=depth) (board:=(Z).graph) (packet:=(Z).width) (f:=f) (C:=C)
      (layerBits:=DescentRecordedRotorLayers.width f cap) headers packets
    PeerOrigins B pad (⟨keys,actor,values⟩ : PriorPeerWords B H digit keyBits) unit arr := by
  intro headers packets values
  let obs:=fun v hi j=>(stencil v hi j).val
  have read:=observed_peer_input B pad snap obs cables shapeRead wireRead
  have both:=peer_fallback_roots B pad snap
  apply recorded_peer_origins B recorded pad μ levels stencil snap.peers cables rank_ unit keys stem won residual one
    bound fit active quotaPositive degreePositive levelRead stamped precision depthFits capFits
  · intro s t
    exact (congrArg (key (Ht:=depth) (l:=(Z).layerBits) s (tag t)) (read _ _)).trans (both.1 s t)
  · intro s t v hi absent
    exact (congrArg (key (Ht:=depth) (l:=(Z).layerBits) s t) (read _ _)).trans (both.2 s t v hi absent)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
