import OAI.Hierarchy.DescentPaidCensusRead
import OAI.Hierarchy.DescentPaidResidentGeometry
import OAI.Hierarchy.DescentPackedCensusFromSigned

namespace OAI
/-! # Occupied and padded census coordinates for the next native chooser -/
namespace Hierarchy.DescentPaidResidentCount
open DescentSixParty DescentHostDirectory DescentSIMDLookup
open DescentPackedZip DescentPackedColony Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k age H G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S age) (groups : J≃Fin G) (hosts : V↪Fin H)
local notation "census" => DescentPacking.PackedMatch.Local.Stage.Census.count A groups hosts

def occupies (h : Fin H) (g : Fin G) (x : Fin (2^k)) (u : W.graph.Site) : Prop :=
  hosts (A.pos u).2=h ∧ groups (A.pos u).1=g ∧ A.block u=x

include S ready in
/-- The original paid-unit price bounds the raw length, so a short count
read by the next stage is a natural value at the chooser's existing precision. -/
theorem record_bound (u : W.graph.Site) : (A.records u).length≤A.wire*(A.z*gadget.b)*A.cap := by
  let weight:=W.siteUnits (fun v=>A.hub (A.pos v).2) A.records A.wire 256 A.hist
  have one : (A.records u).length≤A.hist*(A.records u).length :=
    calc
      _ = 1*(A.records u).length := (Nat.one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ ready.atom
  have unit : A.hist*(A.records u).length≤weight u:=Nat.le_add_left _ _
  have single:=Finset.single_le_sum (s:=Finset.univ)
    (f:=fun v : W.graph.Site=>if A.pos v=A.pos u ∧ A.block v=A.block u then weight v else 0)
    (fun j _=>Nat.zero_le _) (Finset.mem_univ u)
  have total : weight u≤StarKeys.blockMass W.graph A.pos A.block weight (A.pos u) (A.block u) := by
    simpa [StarKeys.blockMass] using single
  exact (one.trans (unit.trans total)).trans (A.small _ _)

include S ready in
theorem live_nat (b : ℕ) (precision : A.wire*(A.z*gadget.b)*A.cap<2^b) (u : W.graph.Site) :
    (census b (hosts (A.pos u).2) (groups (A.pos u).1) (A.block u)).val=(A.records u).length := by
  rw [live A S ready]
  exact Fin.val_cast_of_lt ((record_bound A S ready u).trans_lt precision)

theorem ghost (b : ℕ) (h : Fin H) (g : Fin G) (x : Fin (2^k))
    (vacant : ¬∃u,occupies A groups hosts h g x u) : census b h g x=0 := by
  by_cases host : ∃v,hosts v=h
  · simp only [DescentPacking.PackedMatch.Local.Stage.Census.count,dite_eq_left host,PackedCensus.histories,StarKeys.blockMass]
    have absent (u : W.graph.Site) : ¬(A.pos u=(groups.symm g,host.choose) ∧ A.block u=x) := by
      rintro ⟨hp,blk⟩
      apply vacant
      refine ⟨u,?_⟩
      simp [occupies,hp,host.choose_spec,blk]
    simp [absent]
  · simp [DescentPacking.PackedMatch.Local.Stage.Census.count,host]

theorem blank {D cap b n : ℕ} (addresses : Fin (DescentPackedActorMask.actors D cap)→Cell n)
    (counts : Fin D→Cell b) :
    counted D cap b (DescentPackedActorMask.target n _ 0 (encode n _ addresses)) (encode b _ counts)=0 := by
  simp [counted,seen]

include S ready in
/-- The native output bank can be plugged into the next chooser at an
ordinary block. Ghost lanes have a zero query even if the donor shelf is nonempty. -/
theorem next_source {D cap b n out : ℕ} (x : Fin (2^k)) (bank : Bank) (mem : Memory w)
    (table : Fin H→Fin G→Fin (DescentPackedActorMask.actors D cap)→Cell n)
    (old : Fin H→Fin G→Fin D→Cell b) (query : Fin H→Fin G→Cell n)
    (hit : ∀u,
      let h:=hosts (A.pos u).2
      let g:=groups (A.pos u).1
      A.block u=x→counted D cap b (DescentPackedActorMask.target n _ (query h g) (encode n _ (table h g)))
        (encode b _ (old h g))=((A.records u).length:ℕ))
    (pad : ∀h g,(¬∃u,occupies A groups hosts h g x u)→query h g=0)
    (fit : bank.Fits w out) (room : H*chunks G M≤bank.size)
    (held : Reads bank (fun h g=>counted D cap b
      (DescentPackedActorMask.target n _ (query h g) (encode n _ (table h g))) (encode b _ (old h g))) M mem) :
    Source (.lookup bank .row) (fun h g=>census b h g x) M mem := by
  have correct (h : Fin H) (g : Fin G) :
      counted D cap b (DescentPackedActorMask.target n _ (query h g) (encode n _ (table h g)))
        (encode b _ (old h g))=census b h g x := by
    by_cases existsSite : ∃u,occupies A groups hosts h g x u
    · obtain ⟨u,hh,hg,hx⟩:=existsSite
      subst h;subst g
      exact (hit u hx).trans (hx ▸ (live A S ready groups hosts b u).symm)
    · rw [pad h g existsSite,blank,ghost A groups hosts b h g x existsSite]
  apply source_column bank out fit mem _ room
  simpa only [DescentPackedColony.Reads, correct] using held

section Ordinary
set_option quotPrecheck false
open DescentKernelHistory DescentCableDonorNames DescentPackedActorMask
variable {J' V' : Type} [Fintype J'] [DecidableEq J'] [Fintype V'] [DecidableEq V']
    {k' age' D b n out : ℕ} (he : 0≤ε) (choice : (A.stage.result he).Choice)
    {N : MarkedWorld F d P bits} (norm : Normalize N)
    (next : GroupStage norm.result gadget price ε J' V' k')
    (receipt : ParticleRows he A.stage choice N norm (fun v=>(next.records v).length) (fun v=>next.hub (next.pos v).2))
variable {I : Type} [Fintype I]
    (later : next.StateBounds S age') (native : W.graph.Edge ↪ ℕ)
    (pick : I × Fin 2 ↪ W.graph.Edge) (picked : ∀ i, pick (i,0) ∈ W.core)
    (dest : W.graph.Site ⊕ (I × Fin 6) → norm.result.graph.Site)
    (groups' : J' ≃ Fin G) (hosts' : V' ↪ Fin H) (halo : Halo norm.result.graph.Site W.graph.Site D)
    (oldHere : ∀ u, u ∈ halo.member (dest (.inl u)))
    (bornHere : ∀ i j, W.graph.src (pick (i,0)) ∈ halo.member (dest (.inr (i,j))))
    (lengths : ∀ v, (next.records v).length = total dest (fun u => (A.records u).length) v)
local notation "locH" v => hosts' (next.pos v).2
local notation "locG" v => groups' (next.pos v).1
local notation "at_" v => DescentOrdinaryLocalBirth.donorAt halo v
local notation "cost" => fun u : W.graph.Site => (A.records u).length
local notation "slot" => DescentOrdinaryLocalBirth.outgoingSlot (I := I) A native S ready pick picked

include later oldHere bornHere lengths in
private theorem ordinary_source_at (x : Fin (2^k')) (bank : Bank) (mem : Memory w)
    (table : Fin H→Fin G→Fin (actors D A.cap)→Cell n) (old : Fin H→Fin G→Fin D→Cell b)
    (query : Fin H→Fin G→Cell n)
    (positive : ∀v,next.block v=x→query (locH v) (locG v)≠0)
    (oldRead : ∀v,next.block v=x→∀i,(old (locH v) (locG v) i).val=((at_ v) i).elim 0 cost)
    (oldDest : ∀v,next.block v=x→∀i,
      table (locH v) (locG v) (oldAddress A.cap i)=query (locH v) (locG v) ↔
        ∃u,(at_ v) i=some u ∧ dest (.inl u)=v)
    (bornDest : ∀v,next.block v=x→∀(i : Fin D) (s : Fin A.cap) (j : Fin 6),
      table (locH v) (locG v) (bornAddress i (finProdFinEquiv (s,j)))=query (locH v) (locG v) ↔
        ∃t : I,(at_ v) i=some (W.graph.src (pick (t,0))) ∧ slot t=s ∧ dest (.inr (t,j))=v)
    (pad : ∀h g,(¬∃v,occupies next groups' hosts' h g x v)→query h g=0)
    (fit : bank.Fits w out) (room : H*chunks G M≤bank.size)
    (held : Reads bank (fun h g=>counted D A.cap b (target n _ (query h g) (encode n _ (table h g)))
      (encode b _ (old h g))) M mem) :
    Source (.lookup bank .row) (fun h g=>DescentPacking.PackedMatch.Local.Stage.Census.count next groups' hosts' b h g x) M mem := by
  apply next_source next S later groups' hosts' x bank mem table old query _ pad fit room held
  intro v
  dsimp only
  intro hx
  have exactCount:=issued (I := I) (C := norm.result.graph.Site) A native S ready pick picked dest halo oldHere bornHere v
    (query (locH v) (locG v)) (table (locH v) (locG v)) (old (locH v) (locG v)) cost
    (positive v hx) (oldDest v hx) (bornDest v hx) (oldRead v hx)
  exact exactCount.trans (congrArg (fun n : ℕ=>(n : Cell b)) (lengths v).symm)


private structure SourceFact where
  statement : Prop
  checked : statement

private def SourceFact.ofProof {p : Prop} (hp : p) : SourceFact := ⟨p,hp⟩

private def ordinaryFact : SourceFact :=
  SourceFact.ofProof (ordinary_source_at (M := M) (w := w) (b := b) (n := n) (out := out)
    A S ready norm next later native pick picked dest groups' hosts' halo oldHere bornHere lengths)

private def scanOrdinaryFact {stagePrice : ℝ} {T : StageInput W gadget stagePrice ε}
    (r : BitDescription.ScanRows he T)
    (venue : W.graph.Site ⊕ (r.pairs × Fin 6) → norm.result.graph.Site)
    (oldScan : ∀ u,u ∈ halo.member (venue (.inl u)))
    (bornScan : ∀ i j,W.graph.src (r.pick (i,0)) ∈ halo.member (venue (.inr (i,j))))
    (countsScan : ∀ v,(next.records v).length = total venue (fun u => (A.records u).length) v) : SourceFact :=
  ordinaryFact (M := M) (w := w) (b := b) (n := n) (out := out) (I := r.pairs)
    A S ready norm next later native r.pick (fun i => r.picked (i,0)) venue groups' hosts' halo oldScan bornScan countsScan

attribute [local irreducible] BitDescription.scannedRows

private def SourceFact.underCoverage {Old Born : Prop} (facts : Old → Born → SourceFact) : SourceFact where
  statement := ∀ (oldHere : Old) (bornHere : Born), (facts oldHere bornHere).statement
  checked := fun oldHere bornHere => (facts oldHere bornHere).checked

private def receiptOrdinaryFact {stagePrice : ℝ} (T : StageInput W gadget stagePrice ε)
    (option : (T.result he).Choice)
    (record : ParticleRows he T option N norm (fun v=>(next.records v).length) (fun v=>next.hub (next.pos v).2))
    (costEq : (fun u=>(T.records u).length) = (fun u=>(A.records u).length)) : SourceFact :=
  SourceFact.underCoverage fun
    (oldLand : ∀ u,u ∈ halo.member ((trajectory he T option record).choose (.inl u)))
    (bornLand : ∀ i j,W.graph.src ((BitDescription.scannedRows he T).pick (i,0)) ∈
      halo.member ((trajectory he T option record).choose (.inr (i,j)))) =>
  scanOrdinaryFact (M := M) (w := w) (b := b) (n := n) (out := out) (T := T)
    A S ready he norm next later native groups' hosts' halo (BitDescription.scannedRows he T)
    (trajectory he T option record).choose oldLand bornLand (by
      intro v
      rw [← costEq]
      exact (trajectory he T option record).choose_spec.2 v)

local notation "rows" => BitDescription.scannedRows he A.stage

set_option maxHeartbeats 1200000 in
private def chosenOrdinaryFact : SourceFact :=
  receiptOrdinaryFact (M := M) (w := w) (b := b) (n := n) (out := out)
    A S ready he norm next later native groups' hosts' halo A.stage choice receipt rfl

attribute [local irreducible] chosenOrdinaryFact
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
/-- The paid census for the scanning trajectory, available in the next chooser's original bank. -/
theorem ordinary_source (_picked : ∀ i : (rows).pairs,(rows).pick (i,(0 : Fin 2)) ∈ W.core)
    (groups' : J' ≃ Fin G) (hosts' : V' ↪ Fin H) (halo : Halo norm.result.graph.Site W.graph.Site D) :
    (chosenOrdinaryFact (M := M) (w := w) (b := b) (n := n) (out := out) A S ready he choice norm next receipt later native groups' hosts' halo).statement := by
  clear _picked
  exact (chosenOrdinaryFact (M := M) (w := w) (b := b) (n := n) (out := out) A S ready he choice norm next receipt later native groups' hosts' halo).checked

end Ordinary
end
end Hierarchy.DescentPaidResidentCount

end OAI
