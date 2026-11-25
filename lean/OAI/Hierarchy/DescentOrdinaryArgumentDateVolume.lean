import OAI.Hierarchy.DescentOriginalDateFactors

namespace OAI
/-! # One scale for the entire true ordinary registered entry and its two shared controls -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryBooks
open Computability.BorderVNP.Crossing DescentDatedAddressBook DescentPacking.PackedMatch.Local
open DescentGatheredVectorReshape DescentOperandVectorArena DescentSIMDLookup DescentArgumentWidthArithmetic
open ProtocolRAM hiding scale
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




private theorem scale_power (J a n : ℕ) : scale J (n*a)=(scale J a)^n :=by
  unfold scale
  rw [←pow_mul]
  congr 1
  ring

/-- The actual shape, physical scalar purchase and signed representation determine
a single choice-independent price for all original table loads and returning rows.
The exponent is independent of the tail scaling constant. -/
theorem argument_date_volume (J a ratio : ℕ) (large : 16384≤ scale J a)
    (sizes : ∀j,(Lₑ).bookMouthParameters j≤ scale J a)
    (degreeFits : src.placement.degree≤(Lₑ).reference.degree)
    (capFits : src.placement.cap≤(Lₑ).reference.capacity) :
    let v:=Tₑ
    let W:=v.registeredFrom ports stageFloor
    let A:=v.registeredEntry ports stageFloor
    let e:=v.argumentUnitFrom ports stageFloor
    ∀(_geo : PhysicalOrdinary.SectionPopulation W A S age)
      (_rad : W.vector.radix=S.radix)
      (_format : W.signed=W.signedLayout.format v.payload)
      (_header : v.material.fieldBits≤ scale J a)
      (_purchase : v.fundedMaxUnit e≤ scale J a)
      (_signedWidth : W.signedLayout.unit≤ scale J a)
      (_ingress : (v.fundedClip e).factor≤ scale J a),
      v.argumentDateCharge ports stageFloor ratio J (4*a) a≤
        scale J (600*a)*ratio*W.rowVolume v.payload :=by
  intro v W A e _geo _rad _format _header _purchase _signedWidth _ingress
  let U:=scale J a
  let K:=U^100
  let Z:=W.rowVolume v.payload
  let r:=2^v.area.k
  let u:=r*v.fundedWorkingUnit e
  have pos : 0<U:=by dsimp [U];omega
  have lift_ {m n x : ℕ} (low : x≤ U^m) (mn : m≤ n) : x≤ U^n:=
    low.trans (Nat.pow_le_pow_right pos mn)
  have small {x : ℕ} (bound : x≤ U) : x≤ U^14:=by
    apply lift_ (m:=1) _ (by decide);simpa using bound
  have up {x : ℕ} (bound : x≤ U^14) : x≤ K:=lift_ bound (by decide : 14≤100)
  have fixed : U^14≤ K:=up le_rfl
  have rU : r≤ U:=sizes 2
  have nonempty : 0<W.vector.radix:=pow_pos (by decide : 0<2) k
  have price₀ : u≤ U^14:=by
    change 2^v.area.k*v.fundedWorkingUnit e≤ U^14
    rw [(v.source_density e).2]
    refine lift_ (m:=3) ?_ (by decide)
    calc _≤ U*(U*U):=Nat.mul_le_mul (show 8≤ U from by dsimp [U];omega) (Nat.mul_le_mul rU _purchase)
         _=_:=by ring
  have panel : v.fundedPanelUnit≤ U:=(Nat.le_max_left ..).trans _purchase
  have cpu : v.area.unit≤ U:=((v.source_density e).1).trans _purchase
  have middle:=registered_middle_volume ticket gain tail p f payload seats hostLanes old ordinary op drift degree
    ports stageFloor U large sizes degreeFits ratio _geo _rad (small _ingress) (small panel) (small cpu) price₀
  have local_:=original_date_factors ticket gain tail p f payload seats hostLanes old ordinary op drift degree
    ports stageFloor U large sizes degreeFits capFits
  have actual:=registered_selector_inputs ticket gain tail p f payload seats hostLanes old ordinary op drift degree
    ports stageFloor U (by omega) sizes degreeFits capFits _header _purchase
  have coef : ∀q,W.ticketReadGeometry.coefficientInputs 32 u q≤ scale J (4*a):=by
    simpa only [scale_power] using actual
  have lowQ : W.vector.lows≤ scale J (4*a):=by
    rw [scale_power]
    have lowBase : W.vector.lows ≤ U := sizes 6
    exact lift_ (m:=1) (by simpa only [pow_one] using lowBase) (by decide : 1≤4)
  have reachedDegree : (Lₑ).reference.degree = W.area.D := congrArg SignedExtent.degree _format
  have sameLows : W.vector.lows = StageVenueTail.OrdinaryRaster.shapes W.area := by
    change (2^(k+1)-1)*DescentOrdinaryVenueReturn.shapeSlots (Lₑ).reference.degree =
      (2^(k+1)-1)*DescentOrdinaryVenueReturn.shapeSlots W.area.D
    rw [reachedDegree]
  have capHead:=W.head_unit_at_scale J (4*a) u _format sameLows coef lowQ
  have headK : W.headUnit≤ K:=by
    rw [show 20*(4*a)=80*a by omega,scale_power] at capHead
    exact lift_ capHead (by decide : 80≤100)
  have selectK : scale J (22*(4*a))≤ K:=by
    rw [show 22*(4*a)=88*a by omega,scale_power]
    exact Nat.pow_le_pow_right pos (by decide)
  have mouthK : scale J (20*a)≤ K:=by
    rw [scale_power];exact Nat.pow_le_pow_right pos (by decide)
  obtain ⟨fieldBound,paths,adj,loops⟩:=local_
  have read:=v.original_control_volume ports stageFloor _geo _rad nonempty J (4*a) ratio K
    (up fieldBound) (up (small panel)) (up (small _signedWidth)) (up paths) (up adj) (up loops)
    (up (small (sizes 5))) (up price₀) selectK
  have heads:=v.original_head_volume ports stageFloor _geo _rad nonempty K ratio headK (up (small _signedWidth)) (up price₀)
  have mouths:=v.origin_mouth_volume ports stageFloor _geo _rad nonempty J a K ratio (up (small rU))
    (up (small (sizes 6))) (up (small (sizes 5))) (up price₀) mouthK
  have broad : (40+20*U^14)*U^14*ratio*Z≤(40+20*K)*K*ratio*Z:=by gcongr
  have total : (40+20*K)*K+PhysicalOrdinary.originalControlRate K+(1+5*K)*K+PhysicalOrdinary.originRate K≤ K^6:=by
    have hK : 16384≤ K:=up (small large)
    generalize K=x at hK ⊢
    obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le hK
    simp only [PhysicalOrdinary.originalControlRate, DescentArgumentWordRectangle.pathRate,
      DescentArgumentWordRectangle.depotRate, DescentArgumentWordRectangle.columnRate, PhysicalOrdinary.originRate]
    ring_nf; omega
  calc
    _≤(40+20*K)*K*ratio*Z+PhysicalOrdinary.originalControlRate K*ratio*Z+
      (1+5*K)*K*ratio*Z+PhysicalOrdinary.originRate K*ratio*Z:=by
        unfold PhysicalOrdinary.argumentDateCharge
        exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (middle.trans broad) read) heads) mouths
    _=((40+20*K)*K+PhysicalOrdinary.originalControlRate K+(1+5*K)*K+PhysicalOrdinary.originRate K)*ratio*Z:=by ring
    _≤ K^6*ratio*Z:=by gcongr
    _=scale J (600*a)*ratio*Z:=by
      change (U^100)^6*ratio*Z=_
      rw [←pow_mul,scale_power J a 600]

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryBooks

end OAI
