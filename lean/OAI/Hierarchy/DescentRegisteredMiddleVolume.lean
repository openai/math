import OAI.Hierarchy.DescentRegisteredMiddleFactors
import OAI.Hierarchy.DescentArgumentRowVolume

namespace OAI
/-! # Word-volume bound for the actual registered ingress, dictionaries, gather and resolver -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryBooks
open Computability.BorderVNP.Crossing DescentDatedAddressBook DescentPacking.PackedMatch.Local
open DescentGatheredVectorReshape DescentOperandVectorArena DescentSIMDLookup ProtocolRAM DescentArgumentWidthArithmetic
open DescentCompiler DescentCompiler.TerminalScale DescentDatedOperandReadPipeline DescentHaloWalkRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule}
    {d k age z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {src : Reached W G q ε S k age z D wire hist} {he : 0≤ ε} {T : StageInput W G u ε}
    {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
    {dst : Reached n.result G q ε S k (age+1) z' D' wire hist}
    (ticket : OrdinaryLink src he T c n dst)
    (gain tail p f payload seats hostLanes : ℕ) (old : Bank)
    (ordinary : ℕ→Stage.Dated.Ordinary)
variable (op : RotorSpec) (drift degree : ℕ) (ports : DatePorts) (stageFloor : ℕ)
local notation "Lₑ" => atDate G S op gain k age p tail drift degree payload seats ports
local notation "Tₑ" => (Lₑ).onTicket ticket gain tail p f payload seats hostLanes old ordinary
local notation "Eₑ" => (Tₑ).datedEntry ports stageFloor




theorem registered_middle_volume (U : ℕ) (large : 16384≤ U)
    (sizes : ∀i,(Lₑ).bookMouthParameters i≤ U)
    (degreeFits : src.placement.degree ≤ (Lₑ).reference.degree)
    (ratio : ℕ) :
    let v:=Tₑ
    let W:=v.registeredFrom ports stageFloor
    let A:=v.registeredEntry ports stageFloor
    let e:=v.argumentUnitFrom ports stageFloor
    let u:=v.fundedWorkingUnit e
    let r:=2^v.area.k
    ∀(_geo : PhysicalOrdinary.SectionPopulation W A S age)
      (_rad : W.vector.radix=S.radix) (_ingress : (v.fundedClip e).factor≤ U^14)
      (_panel : v.fundedPanelUnit≤ U^14) (_alu : v.area.unit≤ U^14)
      (_price : r*u≤ U^14),
      v.registeredEntryCharge ports stageFloor ratio≤
        (40+20*U^14)*U^14*ratio*(W.rowVolume v.payload) :=by
  intro v W A e u r _geo _rad _ingress _panel _alu _price
  let h:=v.payload
  let Z:=W.rowVolume h
  let K:=U^14
  have occupancy : u≤ K:=(Nat.le_mul_of_pos_left u (by dsimp [r]; positivity)).trans _price
  have flags:=_geo.native_rows h _rad (show 0<W.vector.radix by change 0<2^k; positivity)
  rcases flags with ⟨origin,priorH,nextH,priorG,nextG,compactH,compactG,wideG,groups,rom,_,_⟩
  have specs:=registered_middle_factors ticket gain tail p f payload seats hostLanes old ordinary op drift degree
    ports stageFloor U large sizes degreeFits
  rcases specs with ⟨_,d₀,d₁,d₂,gath,resolv,pages⟩
  let L:=A.population W stageFloor
  let B:=W.bornBook
  have hosts : L.hosts=W.material.oldHosts:=_geo.clip.1
  have oldGroups : L.groups=W.material.oldGroups:=_geo.clip.2
  have r₀ : h+L.hosts*h+L.hosts*L.groups*u≤(2+u)*Z:=
    DescentArgumentWordRectangle.rows origin (by rw [hosts];exact priorH) (by rw [hosts,oldGroups];exact priorG) u
  have r₁ : h+B.hosts*h+B.hosts*B.groups*u≤(2+u)*Z:=by
    rw [show B.hosts=W.material.oldHosts from _geo.born.1,show B.groups=W.material.oldGroups from _geo.born.2]
    exact DescentArgumentWordRectangle.rows origin priorH priorG u
  have dict : W.dictionaryCharge A h u ratio≤(7+2*K)*K*ratio*Z:=by
    unfold PhysicalOrdinary.dictionaryCharge
    dsimp only
    rw [Nat.mul_assoc _ (2^(h/2)) h]
    exact DescentArgumentWordRectangle.three_terms d₀ d₁ d₂ r₀ r₁ rom occupancy
  have vectorRows : h+2*W.vector.hosts*h+W.vector.hosts*(W.vector.groups*W.vector.radix)*u+
      W.vector.hosts*W.vector.groups*(r*u)≤(3+2*K)*Z:=by
    have vh : W.vector.hosts*h≤ Z:=by rw [_geo.vector.1];exact priorH
    exact (DescentArgumentWordRectangle.squareRows origin vh wideG groups u (r*u)).trans
      (Nat.mul_le_mul_right Z (by omega))
  have gv : W.gatherCharge h u (r*u) ratio≤(4+2*K)*K*ratio*Z:=by
    unfold PhysicalOrdinary.gatherCharge
    dsimp only
    rw [Nat.mul_assoc _ (2^(h/2)) h]
    calc
      _≤ K*ratio*((3+2*K)*Z)+K*ratio*Z:=by gcongr
      _=_:=by ring
  have finishRows : h+W.resolver.hosts*h+W.resolver.hosts*W.resolver.groups*(r*u)≤(2+K)*Z:=
    (DescentArgumentWordRectangle.rows origin compactH compactG _).trans
      (Nat.mul_le_mul_right Z (Nat.add_le_add_left _price 2))
  have rs : W.resolverCharge h (r*u) ratio≤(3+K)*K*ratio*Z:=by
    unfold PhysicalOrdinary.resolverCharge
    dsimp only
    rw [Nat.mul_assoc _ (2^(h/2)) h]
    exact DescentArgumentWordRectangle.two_terms resolv pages finishRows rom
  have hrow : (v.fundedClip e).venue.hosts*h≤ Z:=by
    change L.hosts*h≤ Z;rw [hosts];exact priorH
  have grow : (v.fundedClip e).venue.hosts*(v.fundedClip e).venue.groups≤ Z:=by
    change L.hosts*L.groups≤ Z;rw [hosts,oldGroups];exact priorG
  have head : v.ingressCharge e h ratio≤(6+9*K)*K*ratio*Z:=by
    let c:=v.fundedClip e
    have val : 4*c.venue.hosts*h=4*(c.venue.hosts*h):=Nat.mul_assoc ..
    unfold PhysicalOrdinary.ingressCharge
    dsimp only
    rw [val,Nat.add_mul,one_mul]
    calc
      _≤ K*ratio*((Z+Z)+4*Z+Z*(K+4*K+4*K)):=by gcongr
      _=_:=by ring
  change v.ingressCharge e h ratio+W.dictionaryCharge A h u ratio+W.gatherCharge h u (r*u) ratio+
    W.resolverCharge h (r*u) ratio≤_
  calc
    _≤(6+9*K)*K*ratio*Z+(7+2*K)*K*ratio*Z+(4+2*K)*K*ratio*Z+(3+K)*K*ratio*Z:=by gcongr
    _≤_:=by change _≤(40+20*K)*K*ratio*Z;ring_nf;omega

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryBooks

end OAI
