import OAI.Hierarchy.DescentResetSelectedPrimeBill
import OAI.Hierarchy.DescentResetSelectedIngressBill
import OAI.Hierarchy.DescentResetSelectedStencilPrice
import OAI.Hierarchy.DescentResetAtlasControlScale
import OAI.Hierarchy.DescentResetRootHeaderScale
import OAI.Hierarchy.DescentResetIncurredRoots
import OAI.Hierarchy.DescentResetRootUnitScale

namespace OAI
/-! The incoming selected reset through the published root dictionary, including
the estimator, Walsh regrouping at the chosen receiver pitch and physical root writes. -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentDatedAddressBook DescentCompiler TerminalScale DescentNamedFundedChart DescentPackedWalsh
open DescentPlainTerminal.Suffix DescentFallbackPeriod DescentStaticWordColumn ProtocolRAM Filter
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (G : PoweredGadget F) {deg : ℕ} {bs : P→ℕ} (W : MarkedWorld F deg P bs) (q ε : ℝ)

/-- No component of the physical root preparation is counted twice. The final six
terms shared across hosts cover the ingress, two solver tables, two stencil tables,
and the prepared root atlas. -/
def RootDatePrice (t f g reset τ B D n d C z ratio receiver saving lead exponent : ℕ) : Prop :=
  ∀ᶠ h : ℕ in atTop,∀ copies i p w state wire hist : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let tb:=tail τ J
      let S:=stageNumbers G t J f g reset copies tb
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      ∀(r : Reached W G q ε S k i state D wire hist) (rates : ResetRates G S k D n d C f g z tb)
        (drift degree nextM packet oldLanes primitiveLanes printedBits : ℕ) (ordinary : ℕ→Dated.Ordinary)
        (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ) (count : Bank),
      let prev:=resetCut S k tb p f h i
      let a:=PhysicalReset.selected G S rates.board k tb i p f g drift degree h prev nextM C packet oldLanes
        primitiveLanes printedBits old io.wire io.roster floor
      let start:=a.stageStart floor
      let src:=a.ingress.source floor
      let sh:=selected_stencil_shape (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old io floor
      let roots:=selected_root_inputs (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old io floor
      let atlas:=selected_atlas (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old io floor count
      let Q:=a.rootPhase sh start count io.hubs g (2^n) roots w
      let book:=PhysicalReset.atlasBook atlas sh start count io.hubs g (2^n) roots w
      let front:=a.ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)
      let unit:=selectedRootUnit G t f g reset τ B D ratio lead exponent J
      i < S.length → i%(S.rounds+1)=S.rounds → p ≤ h → 2^h ≤ copies → w ≤ ratio*h →
      old.degree=D → old.paidBits=S.censusBits p → old.lanes=incoming S k tb p f h ordinary i →
      r.placement.cap=((capCalendar G.b S.rounds g S.height).take i).prod*256 →
      (∀x : Fin (2^k),(io.atoms x.val).work ≤ 7) →
      8*S.localWalshBits p (S.groupWidth k tb i+k) f (quota t) ≤ h →
      8*a.successor.groupWidth ≤ h → a.successor.groupWidth ≤ TerminalScale.scale J receiver →
      a.PrimeRoom start src count (S.groupCount i) D w → ∀room : Q.PreparedFits book,
      let body:=a.throughPublishedRoots sh start count io.hubs g (2^n) roots book src (S.groupCount i) D w room
      let ticks:=a.throughPublishedTicks sh start count io.hubs g (2^n) roots book (S.groupCount i) D w room
      (front.ticks+ticks+7*names (front.program.seq body))*w ≤
        S.hostSize i*h*unit+S.hostSize i*(S.groupCount i*S.radix)*unit+6*(copies/(2^J)^saving)

def RootDatePriceAll (t f g reset τ B D n d C z ratio receiver saving lead exponent : ℕ) : Prop :=
  ∀ᶠ h : ℕ in atTop,∀ (P₀ : Type) (d₀ : ℕ) (bs₀ : P₀→ℕ) (world : MarkedWorld F d₀ P₀ bs₀) (q₀ ε₀ : ℝ),∀ copies i p w state wire hist : ℕ,
      let J:=Nat.log 2 h/(2*B)
      let tb:=tail τ J
      let S:=stageNumbers G t J f g reset copies tb
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      ∀(r : Reached world G q₀ ε₀ S k i state D wire hist) (rates : ResetRates G S k D n d C f g z tb)
        (drift degree nextM packet oldLanes primitiveLanes printedBits : ℕ) (ordinary : ℕ→Dated.Ordinary)
        (old : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ) (count : Bank),
      let prev:=resetCut S k tb p f h i
      let a:=PhysicalReset.selected G S rates.board k tb i p f g drift degree h prev nextM C packet oldLanes
        primitiveLanes printedBits old io.wire io.roster floor
      let start:=a.stageStart floor
      let src:=a.ingress.source floor
      let sh:=selected_stencil_shape (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old io floor
      let roots:=selected_root_inputs (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old io floor
      let atlas:=selected_atlas (i:=i) rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old io floor count
      let Q:=a.rootPhase sh start count io.hubs g (2^n) roots w
      let book:=PhysicalReset.atlasBook atlas sh start count io.hubs g (2^n) roots w
      let front:=a.ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)
      let unit:=selectedRootUnit G t f g reset τ B D ratio lead exponent J
      i < S.length → i%(S.rounds+1)=S.rounds → p ≤ h → 2^h ≤ copies → w ≤ ratio*h →
      old.degree=D → old.paidBits=S.censusBits p → old.lanes=incoming S k tb p f h ordinary i →
      r.placement.cap=((capCalendar G.b S.rounds g S.height).take i).prod*256 →
      (∀x : Fin (2^k),(io.atoms x.val).work ≤ 7) →
      8*S.localWalshBits p (S.groupWidth k tb i+k) f (quota t) ≤ h →
      8*a.successor.groupWidth ≤ h → a.successor.groupWidth ≤ TerminalScale.scale J receiver →
      a.PrimeRoom start src count (S.groupCount i) D w → ∀room : Q.PreparedFits book,
      let body:=a.throughPublishedRoots sh start count io.hubs g (2^n) roots book src (S.groupCount i) D w room
      let ticks:=a.throughPublishedTicks sh start count io.hubs g (2^n) roots book (S.groupCount i) D w room
      (front.ticks+ticks+7*names (front.program.seq body))*w ≤
        S.hostSize i*h*unit+S.hostSize i*(S.groupCount i*S.radix)*unit+6*(copies/(2^J)^saving)

private theorem selected_root_sum (J H V shared ingress prime remix sLead aLead sExp aExp : ℕ)
    {front solver stencil atlas : ℕ}
    (hi : front ≤ H*ingress + V*ingress + shared)
    (hp : solver ≤ H*prime + V*prime + 2*shared)
    (hs : stencil ≤ H*(sLead*TerminalScale.scale J sExp+remix) + V*(sLead*TerminalScale.scale J sExp+remix) + 2*shared)
    (ha : atlas ≤ H*(aLead*TerminalScale.scale J aExp) + V*(aLead*TerminalScale.scale J aExp) + shared) :
    let unit := ingress + prime + remix + (sLead+aLead)*TerminalScale.scale J (max sExp aExp)
    front + solver + stencil + atlas ≤ H*unit + V*unit + 6*shared := by
  intro unit
  have mono {x y : ℕ} (order : x ≤ y) : TerminalScale.scale J x ≤ TerminalScale.scale J y :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.mul_le_mul_right (J+1) order)
  let v := sLead*TerminalScale.scale J sExp
  let a := aLead*TerminalScale.scale J aExp
  have leads : v+a ≤ (sLead+aLead)*TerminalScale.scale J (max sExp aExp) := by
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left sLead (mono (le_max_left sExp aExp)))
      (Nat.mul_le_mul_left aLead (mono (le_max_right sExp aExp)))
  have fit : ingress+prime+(v+remix)+a ≤ unit := by
    calc
      _ = (ingress+prime+remix)+(v+a) := by ac_rfl
      _ ≤ _ := Nat.add_le_add_left leads _
  refine (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hi hp) hs) ha).trans ?_
  calc
    _ = H*(ingress+prime+(v+remix)+a) + V*(ingress+prime+(v+remix)+a) + 6*shared := by
      dsimp only [v, a]
      ring
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left H fit)
      (Nat.mul_le_mul_left V fit)) _

/-- The two layout constants are fixed before either height parameter is chosen. -/
theorem selected_root_uniform_all (t f g reset D n d C z ratio receiver saving : ℕ) :
    ∃lead exponent : ℕ,∀τ B,0 < τ → 0 < B →
      2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g) ≤ B →
      2*(3*stencilRate G t f g reset+1) ≤ B →
      RootDatePriceAll G t f g reset τ B D n d C z ratio receiver saving lead exponent := by
  let rate:=13*localRate G t f g reset D n
  obtain ⟨aLead,aExp,quote⟩:=selected_atlas_date_price D n f g rate receiver ratio saving
  obtain ⟨sLead,sExp,stencilPrice⟩:=selected_stencil_uniform G t f g reset D n ratio receiver saving
  refine ⟨sLead+aLead,max sExp aExp,?_⟩
  intro τ B tailPos den laneRoom tableRoom
  unfold RootDatePriceAll
  filter_upwards [quote,stencilPrice τ B den tableRoom,selected_ingress_date_tariff_all G t f g reset τ B D n d C z ratio saving tailPos den,
    selected_prime_date_tariff_all G t f g reset τ B D n d C z ratio saving tailPos den laneRoom,
    ResetMiddle.atlas_controls_at G t f g reset τ B D n den,matrix_and_total G t f g reset B τ] with h aq sq iq pq controls layout
  intro P₀ d₀ bs₀ world q₀ ε₀ copies i p w state wire hist J tb S k r rates drift degree nextM packet oldLanes primitiveLanes printedBits
    ordinary old io floor count prev a start src sh roots atlas Q book front unit live boundary payload ambient hardware degreeAt
    precision pitch capacity work bitsRoom rootRoom width solver room body ticks
  let e:=PhysicalReset.receiverCut G S rates.board k tb i p f g drift degree h prev nextM C packet
    oldLanes primitiveLanes printedBits old
  have height:J ≤ Nat.log 2 h:=Nat.div_le_self ..
  have tailFit:tb ≤ τ*(Nat.log 2 h+1)^2:=Nat.mul_le_mul_left _ ((Nat.succ_le_succ height).trans (by nlinarith))
  obtain ⟨dim,ranges⟩:=layout copies tb i p payload tailFit live.le
  have unitControls:=controls copies i p e prev payload
  let mid:=ResetMiddle.fromCalendar S k tb i p f old.degree h e prev n (GroupStage.depthBound old.degree n f g)
    (capCalendar G.b S.rounds g S.height)
  have same:a.successor.middle=mid:=rfl
  have staged:a.successor.middle.rootControlBits (((capCalendar G.b S.rounds g S.height).take i).prod*256) ≤ TerminalScale.scale J rate ∧
      2^k ≤ TerminalScale.scale J rate ∧ S.localWalshBits p (S.groupWidth k tb i+k) f (quota S.rounds) ≤ TerminalScale.scale J rate := by
    rw [same]
    dsimp only [mid]
    rw [degreeAt]
    exact unitControls
  have inBill:=iq P₀ d₀ bs₀ world q₀ ε₀ copies i p w state wire hist r rates drift degree nextM packet oldLanes primitiveLanes printedBits
    ordinary old io floor live boundary payload ambient hardware bitsRoom degreeAt precision pitch capacity work
  have solverBill:=pq P₀ d₀ bs₀ world q₀ ε₀ copies i p w state wire hist r rates drift degree nextM packet oldLanes primitiveLanes printedBits
    old io floor count live.le payload ambient hardware degreeAt capacity solver
  have stencilBill:=sq copies i p w d C z rates drift degree nextM packet oldLanes primitiveLanes printedBits old io floor count
    live payload ambient hardware degreeAt bitsRoom rootRoom width
  have atlasBill:=selected_atlas_invoice r rates p h drift degree nextM packet oldLanes primitiveLanes printedBits old io floor count
    w rate receiver saving aLead aExp (aq J copies w height ambient hardware) live degreeAt capacity bitsRoom rootRoom dim ranges
    staged width rfl (S.group_power (k:=k) (tail:=tb) rfl rfl i).symm room
  refine (a.incurred_root_bits floor io sh count io.hubs g (2^n) roots book (S.groupCount i) D w room).le.trans ?_
  exact selected_root_sum J (S.hostSize i*h) (S.hostSize i*(S.groupCount i*S.radix))
    (copies/(2^J)^saving) (ingressUnit G t f g reset τ B (quota t) ratio J)
    (PhysicalReset.primeUnit G t f g reset τ B D ratio J)
    (remixFactor ratio*TerminalScale.scale J (5*stencilRate G t f g reset)) sLead aLead sExp aExp
    inBill solverBill stencilBill atlasBill

theorem selected_root_uniform (t f g reset D n d C z ratio receiver saving : ℕ) :
    ∃lead exponent : ℕ,∀τ B,0 < τ → 0 < B →
      2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g) ≤ B →
      2*(3*stencilRate G t f g reset+1) ≤ B →
      RootDatePrice G W q ε t f g reset τ B D n d C z ratio receiver saving lead exponent := by
  obtain ⟨a,b,price⟩:=selected_root_uniform_all G t f g reset D n d C z ratio receiver saving
  refine ⟨a,b,?_⟩
  intro τ B time den lanes tables
  exact (price τ B time den lanes tables).mono fun _ h=>h P deg bs W q ε

theorem selected_root_date_tariff (t f g reset τ B D n d C z ratio receiver saving : ℕ)
    (tailPos : 0 < τ) (den : 0 < B)
    (laneRoom : 2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g) ≤ B)
    (tableRoom : 2*(3*stencilRate G t f g reset+1) ≤ B) :
    ∃lead exponent : ℕ, RootDatePrice G W q ε t f g reset τ B D n d C z ratio receiver saving lead exponent := by
  obtain ⟨lead,ex,late⟩:=selected_root_uniform G W q ε t f g reset D n d C z ratio receiver saving
  exact ⟨lead,ex,late τ B tailPos den laneRoom tableRoom⟩

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
