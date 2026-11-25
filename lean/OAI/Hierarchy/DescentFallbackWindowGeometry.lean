import OAI.Hierarchy.DescentFallbackWindowSources
import OAI.Hierarchy.DescentFallbackMeasuredPresence
import OAI.Hierarchy.DescentRankOperandGeometry

namespace OAI
namespace Hierarchy.DescentFallbackPeriod
open DescentSIMDLookup DescentPackedLeafSelector DescentSharedBookScan DescentResetHostSize
private theorem word_slot {D L cap n r field : ℕ} (p : Packet D L cap n r field) (s : Bool)
    (t : Code r × Option (Fin (2^n))) (root peerCode : Fin (DescentFallbackShapeTable.rows r (2^n)))
    (i : Fin L) (z : Fin (2*cap)) (j : Fin D) (ownCode tariff : ℕ) (localBad remoteBad : Bool)
    (ownRead : localWord p i = 2*ownCode+localBad.toNat)
    (peerRead : arrival p s i z = some (j,2*peerCode.val+remoteBad.toNat))
    (rankRead : score p (root,j.succ,peerCode)=tariff) :
    sourceCell p s t root i z = ⟨true,decide (ownCode=rootCell r n t),localBad,remoteBad,tariff⟩ := by
  have coord (v : ℕ) (b : Bool) : (2*v+b.toNat)/2=v := by cases b <;> simp; omega
  have flag (v : ℕ) (b : Bool) : decide ((2*v+b.toNat)%2=1)=b := by cases b <;> simp
  simp only [sourceCell,ownRead,peerRead,Option.isSome_some,Option.elim_some,coord,flag,
    dite_eq_left peerCode.isLt,Fin.eta,rankRead]
private theorem empty_slot {D L cap n r field : ℕ} (p : Packet D L cap n r field) (s : Bool)
    (t : Code r × Option (Fin (2^n))) (root : Fin (DescentFallbackShapeTable.rows r (2^n)))
    (i : Fin L) (z : Fin (2*cap)) (H total : ℕ) (h : arrival p s i z = none) :
    pick H total (sourceCell p s t root i z)=none := by simp [sourceCell,h,pick]
end Hierarchy.DescentFallbackPeriod

/-! # The raw signed-window selectors on the reached old wire families -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSharedCableNames.Stage DescentGL DescentColonies
open DescentChosenRouter DescentRelativeContacts DescentRouterSlots DescentSharedBookScan DescentSharedLeafLookup
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentStageEdgeReceipt DescentFallbackShapeTable
open DescentRosterOrder DescentResetHostSize DescentPackedLeafSelector
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht H field : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready)) (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u : W.graph.Site=>(A.pos u).2) (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
variable (groupKey : J↪ℕ) (vertex : V↪Fin H)
local notation "ids" => vertex.trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank groupKey ids)
local notation "c" => T.commonDepth
local notation "r" => Z.k-c
local notation "Y" => 2^Z.n
local notation "L" => 2^(m-c)
local notation "fit" => frm.enough.trans (Nat.sub_le ..)
local notation "points" => Fin (L*(2*A.cap))
local notation "old" => Host J V k
local notation "here" => donor digits frm.basis fit
local notation "shelved" => signedPanel A native S ready names
local notation "short" => fun t : Z.Fallback=>shortName c (T.code t)
local notation "term" => fallbackCell A S ready digits Z T frm
local notation "bad" => exceptionalCell A S ready digits Z T frm
local notation "shape" => chartShape A S ready Z T
local notation "wireWord" => peerShapeWord A S ready digits Z T frm
local notation "arrive" => chartArrival A S ready native groupKey vertex
local notation "physical" => signedPeer A native S ready names
local notation "hostAt" => fun t : Z.Fallback=>frm.host.symm (Prod.fst (T.code t))
local notation "rootAt" => selectedRoot A S ready Z T
local notation "hs" => hostRoster A ids
local notation "ticketAt" => chartTicket A S ready digits native Z T frm groupKey vertex
local notation "rankAt" => leafRankAt A S ready Z T
variable (word : Host J V k→ℕ) (rank : Fin H→Fin (width (Z.k-T.commonDepth) (2^Z.n) A.degree)→Cell (Ht+2))

def fallbackPadded {U : Type} (f : V→U) (empty : U) (t : Fin H) :=
  if used : ∃v,vertex v=t then f used.choose else empty

omit [DecidableEq V] in
@[simp] theorem fallbackPadded_hit {U : Type} (f : V→U) (empty : U) (v : V) :
    fallbackPadded vertex f empty (vertex v)=f v := by
  let has : ∃z,vertex z=vertex v:=⟨v,rfl⟩
  rw [fallbackPadded,dite_eq_left has,vertex.injective has.choose_spec]

def fallbackWindow (v : V) (hi : Block c) : DescentFallbackPeriod.Packet A.degree L A.cap Z.n r field :=
  DescentFallbackPeriod.inputs (G:=2^c) (field:=field)
    (fun (h : Fin H) (b : Block c) (j : Fin L)=>fallbackPadded vertex (fun v=>word (here v b j)) 0 h)
    (fun (h : Fin H) (j : Fin A.degree)=>fallbackPadded vertex (fun v=>(hs v j).map vertex) none h)
    (fun (h : Fin H) (b : Block c) (j : Fin L) (z : Fin (2*A.cap))=>fallbackPadded vertex (fun v=>shelved (here v b j) z) none h)
    (fun (h : Fin H) (j : Fin (width r Y A.degree))=>(rank h j).val) (vertex v) hi

local notation "win" => fallbackWindow (field:=field) A S ready digits native Z T frm groupKey vertex word rank
/-- Only real predecessor vertices are selected. The packed scheduler may use any common
rectangular envelope, and rows at physically absent predecessor vertices are kept separate. -/
theorem window_input {u : Fin H→Block c→Fin L→ℕ} {rs : Fin H→Fin A.degree→Option (Fin H)}
    {marked : Fin H→Block c→Fin L→Fin (2*A.cap)→Option (Live A.degree A.cap)}
    (own : ∀v a i,u (vertex v) a i=word (here v a i))
    (chart : ∀v j,rs (vertex v) j=(hs v j).map vertex)
    (raw : ∀v a i j,marked (vertex v) a i j=shelved (here v a i) j)
    (v : V) (a : Block c) :
    DescentFallbackPeriod.inputs (field:=field) u rs marked (fun h i=>(rank h i).val) (vertex v) a=win v a := by
  funext j
  rcases j with (i|⟨k,i⟩)|(⟨i,z⟩|i)
  · simp [fallbackWindow,DescentFallbackPeriod.inputs,own]
  · simp only [fallbackWindow,DescentFallbackPeriod.inputs,chart,fallbackPadded_hit]
    cases peer : hs v k <;> simp [own,fallbackPadded_hit]
  · simp [fallbackWindow,DescentFallbackPeriod.inputs,raw]
  · rfl

variable (room : ∀u,word u+1<2^field) (signBits : DescentSignedCableCodec.width A.degree A.cap≤field)

include room in
theorem window_own (v : V) (hi : Block c) (j : Fin L) :
    DescentFallbackPeriod.localWord (win v hi) j=word (here v hi j) := by
  simp only [fallbackWindow,DescentFallbackPeriod.localWord,DescentFallbackPeriod.inputs,
    fallbackPadded_hit,Fin.val_cast_of_lt (Nat.lt_of_succ_lt (room _))]

include room signBits in
theorem window_arrival (v : V) (hi : Block c) (j : Fin L) (z : Fin (2*A.cap)) (s : Bool) :
    DescentFallbackPeriod.arrival (win v hi) s j z=
      (arrive s (here v hi j) z).map (fun p=>(p.1,word p.2)) := by
  have small (t : Fin H) : fallbackPadded vertex (fun v=>word (here v hi j)) 0 t + 1 < 2^field := by
    unfold fallbackPadded
    split
    · exact room _
    · exact (by have:=room (here v hi j);omega)
  rw [fallbackWindow,DescentFallbackPeriod.arrival_read _ _ _ _ _ _ _ _ _ small signBits]
  simp only [fallbackPadded_hit]
  unfold chartArrival
  cases take : shelved (here v hi j) z with
  | none=>rfl
  | some chip=>
    by_cases side : chip.target = s
    · cases peer : hs v chip.neighbor <;>
        simp [bind,Option.bind_some,Option.pure_def,side,peer,donor,fallbackPadded_hit]
    · simp [bind,Option.bind_some,side]

private theorem arrival_grain (s : Bool) (u : old) (z : Fin (2*A.cap)) {p : Fin A.degree×old}
    (arrived : arrive s u z=some p) :
    ∃e : Grain A,u=home A (endSite A s e) ∧ p.2=home A (endSite A (!s) e) := by
  have remote : physical s u z=some p.2 :=
    (chartArrival_peer A S ready native groupKey vertex s u z).symm.trans
      (congrArg (Option.map Prod.snd) arrived)
  rw [signedPeer_slot] at remote
  obtain ⟨e,used,other⟩:=Option.map_eq_some_iff.mp remote
  have atHere:=(atSlot_iff A native S ready s u z e).mp used
  exact ⟨e,(congrArg Prod.fst atHere).symm.trans (port_fst A s e),other.symm⟩

private theorem code_same {x y : Z.Fallback} (host : (short x).1=(short y).1) :
    (shape x).val=(shape y).val ↔short x=short y := by
  constructor
  · intro same
    exact Prod.ext host (by rw [←chartShape_read A S ready Z T x,←chartShape_read A S ready Z T y,same])
  · intro same
    exact congrArg (fun p=>cell r p.2) same

variable (onWire : ∀s (e : Grain A),word (home A (endSite A s e))=peerShapeWord A S ready digits Z T frm s (home A (endSite A s e)))
variable (countBits : Ht+2≤field)

include countBits in
theorem window_rank (v : V) (hi : Block c) (p : Fields r Y A.degree) :
    DescentFallbackPeriod.score (win v hi) p=(rank (vertex v) (fieldId p)).val :=
  DescentFallbackPeriod.rank_read _ _ _ _ _ _ p
    ((rank (vertex v) (fieldId p)).isLt.trans_le (Nat.pow_le_pow_right (by decide) countBits))

set_option maxHeartbeats 220000 in
include room signBits onWire countBits in
theorem window_slot (s : Bool) (t : Z.Fallback) (j : Fin L) (z : Fin (2*A.cap))
    (before : let u:=oldCellAt A S ready digits Z T frm t j
      (choose (width r Y A.degree) (ticketAt s t u z) (encode (Ht+2) _ (rank (vertex (hostAt t))))).val=
      (signedFields A S ready digits native Z T frm names s t (finProdFinEquiv (j,z))).before) :
    let tkt:=(Z.fallLabel T t,(T.code t).2.2)
    let packet:=win (hostAt t) (rootAt t)
    let amount:=(T.leaves.window (short t)).card
    pick Ht amount (DescentFallbackPeriod.sourceCell packet s tkt (shape t) j z)=
      leafPanel A S ready digits native Z T frm s t (finProdFinEquiv (j,z)) := by
  let u:=oldCellAt A S ready digits Z T frm t j
  let y:=win (hostAt t) (rootAt t)
  have arr : DescentFallbackPeriod.arrival y s j z=(arrive s u z).map (fun p=>(p.1,word p.2)) :=
    window_arrival A S ready digits native Z T frm groupKey vertex word rank room signBits _ _ _ _ _
  have value : DescentFallbackPeriod.localWord y j=word u:=
    window_own A S ready digits native Z T frm groupKey vertex word rank room _ _ _
  have orig:=chartArrival_peer A S ready native groupKey vertex s u z
  have form : signedFields A S ready digits native Z T frm names s t (finProdFinEquiv (j,z)) =
      ⟨(physical s u z).isSome,decide (short (term s u) = short t),bad u,
        (physical s u z).elim false bad,(physical s u z).elim 0 (fun v=>rankAt (short t) (short (term (!s) v)))⟩ := by
    simp only [signedFields,Equiv.symm_apply_apply,u]
  refine Eq.trans ?_ (signedFields_pick A S ready digits native Z T frm names s t (finProdFinEquiv (j,z)))
  change pick _ _ (DescentFallbackPeriod.sourceCell y s _ (shape t) j z)=_
  obtain found | ⟨p,found⟩ := Option.eq_none_or_eq_some (arrive s u z)
  ·
    have no : physical s u z=none:=orig.symm.trans (congrArg (Option.map Prod.snd) found)
    have absent : DescentFallbackPeriod.arrival y s j z = none := by rw [arr,found]; rfl
    rw [DescentFallbackPeriod.empty_slot _ _ _ _ _ _ _ _ absent, form, no]
    rfl
  ·
    obtain ⟨e,hereEq,thereEq⟩:=arrival_grain A S ready native groupKey vertex s u z found
    have ownEq : word u=wireWord s u:=(congrArg word hereEq).trans ((onWire s e).trans (congrArg (wireWord s) hereEq.symm))
    have peerEq : word p.2=wireWord (!s) p.2:=(congrArg word thereEq).trans ((onWire (!s) e).trans (congrArg (wireWord (!s)) thereEq.symm))
    have remote : physical s u z=some p.2:=orig.symm.trans (congrArg (Option.map Prod.snd) found)
    have sameHost : (short (term s u)).1=(short t).1 := by
      have terminal := (congrArg (term s) hereEq).trans (cell_home A S ready digits Z T frm s e)
      have pos := (congrArg (fun point : old => point.1.2) hereEq).symm
      exact (congrArg (fun t : Z.Fallback => (T.code t).1) terminal).trans
        ((frm.homeHost _).trans ((congrArg frm.host pos).trans (frm.host.apply_symm_apply _)))
    have isRoot:=code_same A S ready Z T (x:=term s u) (y:=t) sameHost
    have ds := chartTicket_read A S ready digits native Z T frm groupKey vertex s t u z
    rw [found] at ds
    dsimp only [Option.elim_some] at ds
    change (choose _ (ticketAt s t u z) _).val=_ at before
    rw [ds,choose_ticket] at before
    have price:=window_rank A S ready digits native Z T frm groupKey vertex word rank countBits (hostAt t)
      (rootAt t) (shape t,p.1.succ,shape (term (!s) p.2))
    have coordinate : DescentFallbackPeriod.rootCell r Z.n (Z.fallLabel T t,(T.code t).2.2)=(shape t).val:=rfl
    have ownRead : DescentFallbackPeriod.localWord y j = 2*(shape (term s u)).val + (bad u).toNat :=
      value.trans ownEq
    have peerRead : DescentFallbackPeriod.arrival y s j z =
        some (p.1,2*(shape (term (!s) p.2)).val + (bad p.2).toNat) := by
      rw [arr,found]; exact congrArg (fun k=>some (p.1,k)) peerEq
    have rankRead : DescentFallbackPeriod.score y (shape t,p.1.succ,shape (term (!s) p.2)) =
        rankAt (short t) (short (term (!s) p.2)) := by
      rw [form, remote] at before
      exact price.trans before
    rw [DescentFallbackPeriod.word_slot _ _ _ _ _ _ _ _ _ _ _ _ ownRead peerRead rankRead, form, remote, coordinate]
    simp only [Option.isSome_some,Option.elim_some,isRoot]

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
