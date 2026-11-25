import OAI.Hierarchy.DescentProfiledOrdinaryEntry
import OAI.Hierarchy.DescentProfiledOrdinaryBookRooms
import OAI.Hierarchy.DescentChosenArgumentVolume
import OAI.Hierarchy.DescentRegisteredEntryPaid
import OAI.Hierarchy.DescentOrdinaryChunkDigit
import OAI.Hierarchy.DescentWalshPrecision
import OAI.Hierarchy.DescentRegisteredOrdinaryResultRoom

namespace OAI
/-! The complete native twelve-phase argument charge at the same selected cut and bus. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology Chronology.RegisterTimeline DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook
open DescentPacking.PackedMatch.Local.Stage DescentPackedColony DescentSIMDLookup Filter
open DescentInitialHost DescentMixedRouter DescentResetInvoice ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 12000
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset τ drift degreeMax B driftR ratio saving : ℕ)
local notation:max "idx" h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h
local notation:max "J_" h:arg => Nat.log 2 h/(2*B)
local notation:max "tb_" h:arg => tail τ (J_ h)
local notation:max "S_" h:arg x:arg => stageNumbers G t (J_ h) f g reset (x:idx h).slot.sites (tb_ h)
local notation:max "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation:max "prior_" x:arg => (x).slot.position.ports
local notation:max "seats_" x:arg => (x).slot.menu.seats (x).slot.age
local notation:max "args_" x:arg => (x).base.registeredEntry (prior_ x) (x).stageFloor
local notation:max "ext_" x:arg => (x).base.argumentUnitFrom (prior_ x) (x).stageFloor
local notation:max "room_" h:arg x:arg => (prior_ x).OrdinaryCodeRoom (x).cut.ticket op g (tb_ h) (x).slot.p f drift (x).slot.degree h (seats_ x) (x).slot.position.floor (x).slot.menu.ordinary
local notation:max "chosen_" => Branch.selectedArgumentRate G t f g reset driftR (Branch.chosenClipRate G t f g reset driftR)
local notation:max "digits_" => 44*argumentDigitRate G t f g reset driftR (NativePitch.FundedBase.public_rate G t f g reset).choose

theorem chosen_argument_phase (largeB : 5≤B) :
    ∀ᶠ h : ℕ in atTop, ∀(x : idx h) (w original : ℕ) (room : (room_ h x) w)
      (pg : Fin (7*x.model.vector.operands)), ArgumentCalendar G op t f g reset τ B drift driftR degreeMax h →
      ∀{paidRatio : ℕ}, ReturnCalendar G t f g reset driftR digits_ τ B paidRatio h →
      drift+1≤ TerminalScale.scale (J_ h) driftR → 0<x.slot.sites → 0<x.slot.p → 2^h≤original → w+1≤ratio*h →
      let capacity : (prior_ x).argumentsPerNode≤x.base.vector.operands := Nat.le_max_left ..
      let mat:=x.base.registered_match (prior_ x) x.stageFloor capacity
      let sh:=x.base.registered_geometry (prior_ x) x.stageFloor
      let W:=x.model
      let A:=args_ x
      let src:=W.nativeTicketExpr x.stageFloor room.signed A mat sh room.blocks
      let prep:=W.nativeTicketPreparation x.stageFloor w room.signed A mat sh room.blocks pg
      (W.argumentPhaseAfterSigned x.stageFloor A mat src prep room.chip sh room.endFit room.packed).wordInvoice ≤
        W.inputFee A x.stageFloor w+ratio*TerminalScale.scale (J_ h) (600*chosen_)*W.rowVolume h+
        2*(original/(2^(J_ h))^saving) := by
  let a := chosen_
  filter_upwards [PhysicalOrdinary.registered_entry_paid_all (F:=F) ratio saving,
    stage_chunk_digit G t f g reset τ B largeB,DescentWalshPrecision.eventually_log_square (4*(7*a))] with h kernel digitRoom logCap
  intro x w original room pg grant paidRatio resources driftOk sitesPos grainPos init bus capacity mat sh W A src prep
  let S := S_ h x
  let J := J_ h
  let v := x.base
  let u := TerminalScale.scale J a
  have jFit : J≤Nat.log 2 h := Nat.div_le_self ..
  have hosts (i : ℕ) : 0<S.hostSize i := by
    apply Nat.mul_pos sitesPos
    exact Nat.pow_pos (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
  have actual := Branch.chosen_argument_numerics x.cut.original G S x.cut.branch x.cut.ticket x.cut.before x.cut.after x.cut.joined
    op (tb_ h) drift x.slot.degree h (seats_ x) (prior_ x).venue.lanes (prior_ x) (prior_ x).io.roster x.slot.menu.ordinary
    x.stageFloor (copies:=x.slot.sites) grant rfl rfl rfl driftOk x.slot.degreeLimit x.slot.grainLimit x.firstWidth (previous_nodes ..)
    x.slot.geometry.room.args x.slot.geometry.room.archive.digits (hosts x.slot.age) ratio
  obtain ⟨volume,params,coeffs,buy⟩ := actual
  have signed := x.cut.ticket.selected_signed_rates (show S=stageNumbers G t J f g reset x.slot.sites (tb_ h) from rfl)
    (show k_ h=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g) from rfl)
    (hostRows (S.hostSize x.slot.age)) (NativePitch.incomingHosts S (x.slot.age+1)) (S.groupCount (x.slot.age+1)) h
  have rb : 2^(k_ h) ≤ TerminalScale.scale J (groupRate G t f g reset) :=Nat.pow_le_pow_right (by decide) (groupBits_linear ..)
  have density := tail_unit_rows ((Nat.mul_le_mul rb buy).trans_eq (scale_mul ..)) signed.1 (incomingRate G t f g reset)
  have laneRoom : TerminalScale.scale J (returnLaneRate G t f g reset digits_) ≤ h :=
    (Nat.le_mul_of_pos_left _ (by decide : 0 < 2)).trans resources.width
  have wide : 4*v.fundedMaxUnit (ext_ x)*2^v.area.k ≤ h := by
    calc
      _ = 4*(2^(k_ h)*v.fundedMaxUnit (ext_ x)) := by change 4*_*2^(k_ h)=_;ring
      _ ≤ 8*(2^(k_ h)*v.fundedMaxUnit (ext_ x)) := Nat.mul_le_mul_right _ (by decide)
      _ ≤ _ := density.1.trans laneRoom
  have newWidth : 2*W.signedLayout.unit≤h := (Nat.mul_le_mul_right _ (by decide : 2≤4)).trans
    (density.2.1.trans laneRoom)
  have oldWidth : 2*W.fundedPanelUnit≤h := by
    have fits : W.fundedPanelUnit ≤ v.fundedMaxUnit (ext_ x) := le_max_left ..
    have radixPos : 0<2^v.area.k := Nat.two_pow_pos _
    exact (Nat.mul_le_mul_left 2 fits).trans ((Nat.mul_le_mul_right _ (by decide : 2≤4)).trans
      ((Nat.le_mul_of_pos_right _ radixPos).trans wide))
  let d₀ := DonorDate.atDate G S g (k_ h) x.slot.age x.slot.p
  have same : W.ticket.donorDate=d₀ := congrArg PhysicalOrdinary.StaticCore.donor x.core
  have area : v.area=d₀.schedule h (seats_ x) (S.censusBits x.slot.p) := congrArg PhysicalOrdinary.StaticCore.area x.core
  have coin : 0<v.venue.paidBits := by
    have ni := Nat.clog_pos (by decide : 1<2) (show 1<x.slot.p+1 by omega)
    change 0<S.censusBits x.slot.p
    unfold AtomSchedule.censusBits
    omega
  have covers : v.venue.paidBits≤v.area.unit := by
    rw [area];exact resources.census x.slot.sites (tb_ h) x.slot.p x.slot.age g x.slot.grainLimit
  have roof : 2^v.area.k+1≤v.area.unit := by rw [area];exact rect_amount d₀
  have cap : 256≤W.prior.placement.cap := by
    rw [show W.prior.placement.cap=d₀.cap from congrArg DonorDate.cap same]
    exact Nat.le_mul_of_pos_left _ (DonorDate.prefix_cap_pos G.b t g J x.slot.age (by have := G.paid;omega))
  have fmt : W.signed=W.signedLayout.format h := (Branch.signed_at x.cut.original G S x.cut.branch
    x.cut.ticket x.cut.before x.cut.after x.cut.joined h).symm
  have live : 0<W.signed.hosts := by
    rw [fmt]
    exact (hosts _).trans_le (NativePitch.hosts_bounds S (x.slot.age+1) x.slot.active).1
  have groups := ((prior_ x).ordinary_header_dimensions x.cut.ticket op g (tb_ h) x.slot.p f drift x.slot.degree h
    (seats_ x) x.slot.position.floor x.slot.menu.ordinary x.slot.active x.cut.radix).2.2.2
  have chunk : (A.population W x.stageFloor).chunkBits ≤ h/4 := by
    have working := (v.funded_argument_bounds (ext_ x) (v.datedEntry (prior_ x) x.stageFloor) coin covers wide).clipped
    change Nat.clog 2 (chunks v.area.G (v.fundedClip (ext_ x)).working+1)≤h/4
    rw [area]
    exact digitRoom x.slot.sites x.slot.age _ working
  have menu : (A.population W x.stageFloor).count ≤ 2^(h/4) := by
    have big : 2048 ≤ u := params 0
    have deg : v.area.D+1 ≤ u := params 1
    have block : 2^v.area.k ≤ u := params 2
    have low : v.vector.lows ≤ u := params 6
    have coeff : (A.population W x.stageFloor).count ≤ 1+u^4*u*2+u := by
      change 1+(((W.prior.placement.degree+1)^4*2^v.area.k)*2+v.vector.lows)≤_
      have degreeAt : W.prior.placement.degree = v.area.D := by
        rw [area]
        exact congrArg DonorDate.degree same
      rw [degreeAt]
      simpa only [Nat.add_assoc] using Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_right 2
        (Nat.mul_le_mul (Nat.pow_le_pow_left deg 4) block)) 1) low
    have power : 1+u^4*u*2+u ≤ u^7 := by
      obtain ⟨m,hu⟩ := Nat.exists_eq_add_of_le big
      rw [hu];ring_nf;omega
    have short : 7*a*(J+1)≤h/4 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
      have pos : 0<Nat.log 2 h+1 := Nat.succ_pos _
      have lower : J+1≤(Nat.log 2 h+1)^2 := by rw [pow_two];exact (Nat.succ_le_succ jFit).trans (Nat.le_mul_of_pos_right _ pos)
      exact (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using (Nat.mul_le_mul_left (4*(7*a)) lower).trans logCap)
    have equal : u^7=2^(7*a*(J+1)) := by dsimp only [u,TerminalScale.scale];rw [← pow_mul];congr 1;ring
    exact coeff.trans (power.trans (equal.le.trans (Nat.pow_le_pow_right (by decide) short)))
  have refs : (W.refChart x.stageFloor).endAddress<2^w := by
    rw [show (W.refChart x.stageFloor).endAddress=W.birthStart x.stageFloor from W.reference.end_eq _]
    have first : W.birthStart x.stageFloor≤W.vectorStart x.stageFloor := by rw [PhysicalOrdinary.vectorStart,W.bornBook.affine];exact Nat.le_add_right ..
    have last : W.normalizedEnd x.stageFloor≤W.endAddress x.stageFloor := by rw [PhysicalOrdinary.endAddress,W.resolver.affine];exact Nat.le_add_right ..
    exact (first.trans ((W.vector_before _).trans ((W.routed_le _).trans last))).trans_lt room.endFit
  have invoice := kernel x.Pins v (prior_ x) x.stageFloor w J a (4*a) original room.signed capacity room.blocks pg
    rfl fmt cap oldWidth newWidth live coin covers wide jFit init bus roof coeffs groups params chunk menu refs
    room.endFit room.packed room.chip
  rw [Nat.mul_comm ratio (TerminalScale.scale J (600*a))]
  exact invoice.trans (Nat.add_le_add_right (Nat.add_le_add_left volume _) _)

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
