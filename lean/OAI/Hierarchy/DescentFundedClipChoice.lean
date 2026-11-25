import OAI.Hierarchy.DescentFundedClipNumbers
import OAI.Hierarchy.DescentFundedRasterScaled
import OAI.Hierarchy.DescentOrdinaryVenueClipDensity
import OAI.Hierarchy.DescentOrdinaryAfterSigned
import OAI.Hierarchy.DescentPhysicalSignedFormat
import OAI.Hierarchy.DescentIssuedPublicDonor
import OAI.Hierarchy.DescentDatedSignedInput

namespace OAI
/-! # The funded physical date at the pitches of its actual two incoming banks -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentPaidResidentCount DescentOrdinaryVenueIngress
open DescentPackedActorMask DescentHaloWalkRAM DescentSharedCableNames
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

def fundedPanelUnit := v.ticket.installedDonorWidth v.short v.profile

def fundedUnit := fundedUnitAt v.area v.venue.paidBits

/-- The panel is the issued donor register. The actor bank is the original
matcher venue. The additional consumer unit can account for argument books. -/
def fundedClip (extra : ℕ) : Clip :=
  fundedClipAt v.area (v.ticket.depotShape v.short) v.fundedPanelUnit v.venue.paidBits extra

theorem fundedClip_named (extra : ℕ) (digit : v.short=max (v.k+3) (Nat.clog 2 (v.area.D+1)))
    (epochs : v.profile=DescentTerminalEpochBits.width v.gadget.C) :
    v.fundedClip extra=fundedClipAt v.area v.ticket.donorDate.format v.ticket.donorDate.amount v.venue.paidBits extra := by
  have shape : v.ticket.depotShape v.short=v.ticket.donorDate.format := by rw [digit]; rfl
  have amount : v.fundedPanelUnit=v.ticket.donorDate.amount := by unfold fundedPanelUnit;rw [digit,epochs]; rfl
  unfold fundedClip
  rw [shape,amount]

/-- Different honest ballots have the same clipped receiver whenever their
ordinary public chart, original donor date and packed fee register agree. -/
theorem fundedClip_eq {F' P' : Type} [Field F'] (u : PhysicalOrdinary F' P') (extra : ℕ)
    (area : v.area=u.area) (donor : v.ticket.donorDate=u.ticket.donorDate) (paid : v.venue.paidBits=u.venue.paidBits)
    (leftDigit : v.short=max (v.k+3) (Nat.clog 2 (v.area.D+1))) (leftEpochs : v.profile=DescentTerminalEpochBits.width v.gadget.C)
    (rightDigit : u.short=max (u.k+3) (Nat.clog 2 (u.area.D+1))) (rightEpochs : u.profile=DescentTerminalEpochBits.width u.gadget.C) :
    v.fundedClip extra=u.fundedClip extra := by
  rw [v.fundedClip_named extra leftDigit leftEpochs,u.fundedClip_named extra rightDigit rightEpochs,area,donor,paid]

/-- Each additional consumer can use its own effective per-lane width. The
origin-mask table uses all the regrouped lanes in its preparation ROM. -/
theorem funded_extra_fit (extra width : ℕ) (fits : width≤extra) :
    let c:=v.fundedClip extra
    width*c.working≤v.payload/4 ∧ (width*c.radix)*c.postPitch≤v.payload/4 ∧ width*c.postPitch≤v.payload/4 := by
  intro c
  have low : extra≤c.consumerUnit := le_max_right ..
  have seat : width≤c.unit := fits.trans (low.trans (le_max_right ..))
  have wide : width*c.working≤v.payload/4 := (Nat.mul_le_mul_right _ seat).trans (by
    rw [Nat.mul_comm];exact c.working_fields.2.2)
  have one : 1≤c.radix := Nat.two_pow_pos _
  have post : c.postPitch≤c.working := by simpa only [Clip.working, Nat.mul_one] using Nat.mul_le_mul_left c.postPitch one
  refine ⟨wide,?_,(Nat.mul_le_mul_left width post).trans wide⟩
  calc _ = width*c.working := by unfold Clip.working;ring
       _ ≤ _ := wide

theorem funded_origin_fit (extra oldNodes ordinalBits newNodes : ℕ)
    (room : max (2*oldNodes) (ordinalBits*newNodes)≤extra) :
    let c:=v.fundedClip extra
    (2*oldNodes)*(c.postPitch*c.radix)≤v.payload/4 ∧
      (ordinalBits*newNodes)*(c.postPitch*c.radix)≤v.payload/4 :=
  ⟨(v.funded_extra_fit extra _ ((le_max_left ..).trans room)).1,
    (v.funded_extra_fit extra _ ((le_max_right ..).trans room)).1⟩

/-- Bind all physical pitch projections to the single choice that is executed. -/
def withFundedClip (extra : ℕ) : PhysicalOrdinary F P :=
  let c:=v.fundedClip extra
  let resolver:DescentDatedPriorOperand.Layout:={v.resolver with
    blocks:=c.radix,operands:=v.vector.operands,hosts:=v.vector.hosts*v.vector.lows,
    groups:=v.vector.groups,lanes:=c.postPitch}
  {v with
    rasterLanes:=c.working,
    reference:={v.reference with lanes:=c.working,degree:=v.area.D,k:=v.area.k},
    bornBook:={v.bornBook with lanes:=c.working,blocks:=2^v.area.k,cap:=v.reference.capacity,args:=v.vector.operands},
    vector:={v.vector with lanes:=c.postPitch,radix:=c.radix},
    resolver:=resolver,
    metadata:={v.metadata with chart:=⟨resolver.blocks,resolver.nodes,resolver.hosts,
      resolver.groups,v.metadata.chart.bits,resolver.lanes⟩},
    origin:=⟨v.origin.preparationWords⟩,
    operandBook:=⟨resolver,v.metadata.chart.bits,v.metadata.chart.bits⟩,
    venue:={v.venue with paidLanes:=c.postPitch,aliveLanes:=c.postPitch}}

theorem funded_vector_shape (extra : ℕ) : (v.withFundedClip extra).VectorShape :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem funded_signed_commute (extra : ℕ) :
    (v.withIssuedSigned).withFundedClip extra=(v.withFundedClip extra).withIssuedSigned := rfl

def fundedWorkingUnit (extra : ℕ) :=
  (v.fundedClip extra).densityUnit (4*v.fundedPanelUnit) (4*v.area.unit)

def fundedMaxUnit (extra : ℕ) :=
  max v.fundedPanelUnit (max v.area.unit (v.fundedClip extra).unit)

/-- All three positive pitches and all eight word-key bounds are derived from
one local width per date, with one native-radix copy of that width. -/
theorem funded_bounds (extra : ℕ) (paid : 0<v.venue.paidBits) (input : v.venue.paidBits≤v.area.unit)
    (wide : 4*v.fundedMaxUnit extra*(2^v.area.k)≤v.payload) :
    (v.withFundedClip extra).FundedCaps v.payload (4*v.area.unit) (v.fundedWorkingUnit extra)
      ((2^v.area.k)*v.fundedWorkingUnit extra) := by
  let c:=v.fundedClip extra
  let r:=c.radix
  let b:=v.venue.paidBits
  let S:=v.fundedMaxUnit extra
  let D:=StageVenueTail.OrdinaryRaster.paths v.area*2^v.area.k
  let A:=actors D v.area.cap
  let n:=StageVenueTail.OrdinaryRaster.nameBits v.area
  have rad : 0<r := Nat.two_pow_pos _
  have dpos : 0<v.fundedPanelUnit := by
    have bound:=(v.ticket.installed_donor_widths v.short v.profile).2.2
    change 0<v.ticket.installedDonorWidth v.short v.profile
    omega
  have upos : 0<v.area.unit := paid.trans_le input
  have donorLe : v.fundedPanelUnit≤S := le_max_left ..
  have oldLe : v.area.unit≤S := (le_max_left ..).trans (le_max_right ..)
  have newLe : c.unit≤S := (le_max_right ..).trans (le_max_right ..)
  have room {u : ℕ} (below : u≤S) : 4*u*r≤v.payload :=
    (Nat.mul_le_mul_right r (Nat.mul_le_mul_left 4 below)).trans wide
  have atLeast {u : ℕ} (pos : 0<u) (below : u≤S) : r≤lanes v.payload u := by
    have w:=room below
    change r≤v.payload/(2*u)
    apply (Nat.le_div_iff_mul_le (by omega : 0<2*u)).2
    calc r*(2*u) = 2*(u*r) := by ring
         _ ≤ 4*(u*r) := by omega
         _ = 4*u*r := by ring
         _ ≤ _ := w
  have panel : r≤c.panelPitch := atLeast dpos donorLe
  have actor : r≤c.actorPitch := atLeast upos oldLe
  have localWide := room newLe
  have working := c.working_pos panel actor localWide
  have post := c.post_pos panel actor localWide
  have occupied {u : ℕ} (pos : 0<u) (below : u≤S) :
      v.payload≤lanes v.payload u*(4*u) := by
    have placed := atLeast pos below
    have live : 0<lanes v.payload u := rad.trans_le placed
    have fits : 2*u≤v.payload := (Nat.div_pos_iff.mp live).2
    exact (occupancy _ _ pos fits).2.trans_eq (by ring)
  have den₀ : v.payload≤c.panelPitch*(4*v.fundedPanelUnit) := occupied dpos donorLe
  have den₁ : v.payload≤c.actorPitch*(4*v.area.unit) := occupied upos oldLe
  have fillM := c.working_density _ _ panel actor localWide den₀ den₁
  have fillP := c.post_density _ _ panel actor localWide den₀ den₁
  have consume : max (b*D+b) (max (n*A) (1*A+b*D))≤c.unit :=
    (show v.fundedUnit≤c.consumerUnit from le_max_left ..).trans (le_max_right ..)
  have tab : b*D+b≤c.unit := (le_max_left ..).trans consume
  have mask : n*A≤c.unit := (le_max_left ..).trans ((le_max_right ..).trans consume)
  have both : 1*A+b*D≤c.unit := (le_max_right ..).trans ((le_max_right ..).trans consume)
  have value : b≤c.unit := (Nat.le_add_left ..).trans tab
  have tableBound {u : ℕ} (small : u≤c.unit) : u*c.working≤v.payload/2 :=
    (Nat.mul_le_mul_right _ small).trans (by
      rw [Nat.mul_comm]
      have fit : c.working*c.unit ≤ v.payload/4 := c.working_fields.2.2
      exact fit.trans (by omega))
  have raw : b*v.area.lanesAt≤v.payload/2 := (Nat.mul_le_mul_right _ input).trans (by
    rw [Nat.mul_comm]
    exact lanes_fit v.payload v.area.unit)
  have inCap : v.area.lanesAt≤v.payload := by
    have lo : 1≤b := paid
    have h:=Nat.mul_le_mul_right v.area.lanesAt lo
    rw [Nat.one_mul] at h
    omega
  have workCap : c.working≤v.payload := c.working_fields.2.1.trans inCap
  have outBits : (b*r)*c.postPitch≤v.payload/2 := calc
    _ = b*c.working := by change (b*c.radix)*c.postPitch=b*(c.postPitch*c.radix);ring
    _ ≤ _ := tableBound value
  exact ⟨rad.trans_le actor,working,post,inCap,workCap,workCap,paid,raw,
    tableBound tab,tableBound mask,tableBound both,tableBound value,outBits,den₁,fillM,fillP⟩

/-- The source banks and existing role directory stay at the addresses issued
by the earlier date. Only the newly emitted program uses the selected clip. -/
private def copyEntry (W : PhysicalOrdinary F P) (c : Clip) (A : ArgumentEntry v) : ArgumentEntry W :=
  ⟨c,A.venue,A.previous,A.previousBase,A.rolePitch,A.roleBits,A.role⟩

/-- The pitch choice and the exact emitted space up to the reference ROM. -/
def withFundedArguments (extra : ℕ) (A : ArgumentEntry v) : PhysicalOrdinary F P :=
  let W:=v.withFundedClip extra
  let entry:=copyEntry v W (v.fundedClip extra) A
  {W with ingressWords:=entry.words W}

def fundedEntry (extra : ℕ) (A : ArgumentEntry v) : ArgumentEntry (v.withFundedArguments extra A) :=
  copyEntry v _ (v.fundedClip extra) A

/-- The two independent choices of signed return format and funded venue
can be applied in either order, including the exact charge up to the ROM. -/
def issuedEntry (A : ArgumentEntry v) : ArgumentEntry v.withIssuedSigned :=
  copyEntry v _ A.clip A

theorem funded_arguments_signed_commute (extra : ℕ) (A : ArgumentEntry v) :
    v.withIssuedSigned.withFundedArguments extra (v.issuedEntry A)=
      (v.withFundedArguments extra A).withIssuedSigned := rfl

/-- The original signed metadata, its address, and its accounting are established
before the selected ordinary receiver consumes either of the two donor banks. -/
theorem funded_signedEnd (extra : ℕ) (A : ArgumentEntry v) (floor : ℕ) :
    (v.withFundedArguments extra A).signedEnd floor=v.signedEnd floor := rfl

theorem funded_signedAt (extra : ℕ) (A : ArgumentEntry v) (floor : ℕ) :
    (v.withFundedArguments extra A).markEnd floor=v.markEnd floor ∧
    (v.withFundedArguments extra A).signed=v.signed := ⟨rfl,rfl⟩

theorem fundedSignedChart (extra : ℕ) (A : ArgumentEntry v) (chart : v.SignedChart) :
    (v.withFundedArguments extra A).SignedChart :=
  ⟨chart.degree,chart.blocks,chart.seats,chart.markSlots⟩

theorem funded_signedPhase (extra : ℕ) (A : ArgumentEntry v) (chart : v.SignedChart) (floor w : ℕ) :
    (v.withFundedArguments extra A).signedPhase floor (v.fundedSignedChart extra A chart) w=
      v.signedPhase floor chart w := rfl

theorem funded_words_eq {F' P' : Type} [Field F'] (u : PhysicalOrdinary F' P') (extra : ℕ)
    (A : ArgumentEntry v) (B : ArgumentEntry u) (clip : v.fundedClip extra=u.fundedClip extra)
    (prior : A.previous=B.previous) (pitch : A.rolePitch=B.rolePitch) (digit : A.roleBits=B.roleBits)
    (nodes : v.reference.oldNodes=u.reference.oldNodes) (counts : v.reference.countBits=u.reference.countBits)
    (lows : v.vector.lows=u.vector.lows) (grain : v.gadget.b=u.gadget.b) :
    (v.withFundedArguments extra A).ingressWords=(u.withFundedArguments extra B).ingressWords := by
  simp only [withFundedArguments,ArgumentEntry.words,ArgumentEntry.population,ArgumentEntry.chip,
    ArgumentEntry.roleLayout,copyEntry,withFundedClip]
  rw [clip,prior,pitch,digit,nodes,counts,lows,grain]

theorem funded_refsStart_eq {F' P' : Type} [Field F'] (u : PhysicalOrdinary F' P') (extra floor : ℕ)
    (A : ArgumentEntry v) (B : ArgumentEntry u) (signed : v.signedEnd floor=u.signedEnd floor)
    (words : (v.withFundedArguments extra A).ingressWords=(u.withFundedArguments extra B).ingressWords) :
    (v.withFundedArguments extra A).refsStart floor=(u.withFundedArguments extra B).refsStart floor := by
  simp only [refsStart,funded_signedEnd,signed,words]

/-- The predecessor determines its persistent block and operand counts. Every
internal pitch, block count and RAM boundary is installed by the current date. -/
theorem funded_match (extra : ℕ) (A : ArgumentEntry v) (floor : ℕ)
    (oldBlocks : A.previous.blocks=2^v.area.k)
    (oldArgs : A.previous.operands≤v.vector.operands) :
    (v.fundedEntry extra A).Match (v.withFundedArguments extra A) floor := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,oldBlocks,oldArgs,rfl,rfl,rfl,?_⟩
  exact (v.fundedEntry extra A).ends_at_refs (v.withFundedArguments extra A) floor rfl

theorem funded_argument_bounds (extra : ℕ) (A : ArgumentEntry v) (paid : 0<v.venue.paidBits)
    (input : v.venue.paidBits≤v.area.unit) (wide : 4*v.fundedMaxUnit extra*(2^v.area.k)≤v.payload) :
    (v.withFundedArguments extra A).FundedCaps v.payload (4*v.area.unit) (v.fundedWorkingUnit extra)
      ((2^v.area.k)*v.fundedWorkingUnit extra) := by
  have caps := v.funded_bounds extra paid input wide
  exact ⟨caps.positive, caps.clipped, caps.out, caps.oldCap, caps.clipCap, caps.outCap,
    caps.paid, caps.raw, caps.table, caps.masks, caps.sums, caps.clipBits, caps.outBits,
    caps.fill₀, caps.fill₁, caps.fill₂⟩


end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
