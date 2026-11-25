import OAI.Hierarchy.DescentOrdinaryVenueIngressChart
import OAI.Hierarchy.DescentPaidHubRepeat
import OAI.Hierarchy.DescentScalarHaloAny
import OAI.Hierarchy.DescentScalarVenueRasterAny

namespace OAI
/-! # One tape program for the earlier hub, matched tickets, four-hop roster and receiving rows -/
namespace Hierarchy.DescentOrdinaryVenueIngress.Chart
open DescentSIMDLookup DescentPackedZip DescentRawCablePanel DescentPackedColony DescentHaloWalkRAM DescentScalarVenueMask
open DescentSixParty.Chronology DescentPaidResidentCount ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable (v : Chart) (B : Inputs) (base : ℕ) {w : ℕ}
local notation "H₀" => v.hosts
local notation "G₀" => v.groups
local notation "M₀" => v.lanes
local notation "D₀" => v.socket.degree
local notation "α₀" => v.actorBase base
local notation "β₀" => v.haloBase base
local notation "γ₀" => v.rasterBase base
local notation "rs₀" => v.shape base

def hubPhase (w : ℕ) : NativePhase w:=⟨HubRepeat.program base H₀ G₀ M₀ B.hub w,HubRepeat.ticks base H₀ G₀ M₀ B.hub,
  HubRepeat.image base H₀ G₀ M₀ B.hub,HubRepeat.cheap base H₀ G₀ M₀ B.hub w⟩

def haloPhase (w : ℕ) : NativePhase w:=⟨DescentScalarHaloProgram.program H₀ G₀ M₀ D₀ B.adjacency β₀ w,
  DescentScalarHaloProgram.ticks H₀ G₀ M₀ D₀ B.adjacency β₀,DescentScalarHaloProgram.image H₀ G₀ M₀ D₀ B.adjacency β₀,
  cheap_seq (cheap_seq (cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (@DescentStaticWordColumn.cheap _ _ _ _)) (@scan_cheap _ _ _ _)) (@scan_cheap _ _ _ _)⟩

def rasterPhase (w : ℕ) : NativePhase w:=⟨Raster.code rs₀ v.k v.gain v.slots v.raw v.names H₀ G₀ M₀ γ₀ w,
  Raster.ticks rs₀ v.k v.gain v.slots v.raw v.names H₀ G₀ M₀ γ₀,Raster.result rs₀ v.k v.gain v.slots v.raw v.names H₀ G₀ M₀ γ₀,
  cheap_seq (cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _)
    (cheap_seq (cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) (@ProtocolRAM.program_cheap _ _)) (@DescentStaticWordColumn.cheap _ _ _ _))) (@scan_cheap _ _ _ _)⟩

def pairedPhase (w : ℕ) : NativePhase w:=DepotRAM.ActorInputs.paired v.socket v.profile v.slots v.raw α₀ B.panel B.actors H₀ G₀ M₀ w

def phase (w : ℕ) : NativePhase w:=(((v.hubPhase B base w).seq (v.pairedPhase B base w)).seq (v.haloPhase B base w)).seq (v.rasterPhase base w)

structure Room (w : ℕ) : Prop where
  prior : ∀b∈[B.panel,B.actors,B.hub,B.adjacency],b.Fits w base
  panelRows : v.rows≤B.panel.size
  actorRows : v.rows≤B.actors.size
  hubRows : H₀≤B.hub.size
  adjacent : H₀*D₀≤B.adjacency.size
  pathsWord : M₀*max (DepotRAM.ActorInputs.bits v.socket) (DescentSharedCableNames.Packed.bits v.paths)≤w/2
  keysWord : M₀*max (DepotRAM.ActorInputs.bits v.socket) (DescentSharedCableNames.Packed.bits v.raw)≤w/2
  smallH : H₀<2^w
  smallD : D₀<2^w
  smallPaths : v.paths<2^w
  space : v.endAddress base<2^w

theorem ceilings : base≤α₀ ∧ α₀≤β₀ ∧ β₀≤γ₀ ∧ γ₀≤(v.fieldBank base).base ∧ (v.fieldBank base).base+v.rows≤v.endAddress base := by
  refine ⟨Nat.le_add_right ..,?_,?_,?_,Nat.add_le_add_left v.rowRoom _⟩
  · rw [haloBase,DepotRAM.ActorInputs.translates];exact Nat.le_add_right ..
  · dsimp only [rasterBase,DescentScalarHaloProgram.stop,DescentScalarHaloProgram.ranksBase,
      DescentScalarHaloProgram.endsBase,DescentScalarHaloPortROM.stop,DescentScalarHaloProgram.statics];omega
  · dsimp only [fieldBank,Raster.output,Receiver.header,Headers.post,Headers.rom,Headers.afterHeaders,Headers.start,DescentPackedChildNeighbor.SIMD.ROM.output]
    repeat first | exact le_rfl | apply Nat.le_add_right_of_le

private theorem lift {x y : ℕ} {b : Bank} (src : b.Fits w x) (pos : x≤y) : b.Fits w y :=⟨src.1,src.2.1,src.2.2.trans pos⟩

theorem ticketRooms (l : DepotRAM.ActorInputs.Label v.socket) :
    let f:=DepotRAM.ActorInputs.routeStart v.socket H₀ G₀ M₀ α₀;let g:=DepotRAM.ActorInputs.keyStart v.socket H₀ G₀ M₀ α₀
    let a:=DepotRAM.ActorInputs.bank v.socket H₀ G₀ M₀ f l;let b:=DepotRAM.ActorInputs.bank v.socket H₀ G₀ M₀ g l
    a.base+a.size≤β₀ ∧ b.base+b.size≤β₀ ∧ v.rows≤a.size ∧ v.rows≤b.size :=by
  intro f g a b
  have count:(finProdFinEquiv l).val*(H₀*chunks G₀ M₀)≤(DepotRAM.ActorInputs.count v.socket)*(H₀*chunks G₀ M₀):=Nat.mul_le_mul_right _ (finProdFinEquiv l).isLt.le
  have roof:2^v.rankWidth≤2^Nat.clog 2 (v.rows+1):=Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 (Nat.le_succ _))
  have step:g≤RoleScans.home (DepotRAM.ActorInputs.bits v.socket) H₀ G₀ M₀ (DepotRAM.ActorInputs.count v.socket) g:=Nat.le_add_right ..
  have fg:(RoleScans.home (DepotRAM.ActorInputs.bits v.socket) H₀ G₀ M₀ (DepotRAM.ActorInputs.count v.socket) f)+DepotRAM.ActorInputs.count v.socket*(H₀*chunks G₀ M₀)=g:=rfl
  change _+_+2^v.rankWidth≤_ ∧ _+_+2^v.rankWidth≤_ ∧ _ ∧ _
  refine ⟨?_,?_,v.rowRoom,v.rowRoom⟩ <;> change _≤RoleScans.home (DepotRAM.ActorInputs.bits v.socket) H₀ G₀ M₀ (DepotRAM.ActorInputs.count v.socket) g+DepotRAM.ActorInputs.count v.socket*(H₀*chunks G₀ M₀)+2^Nat.clog 2 (v.rows+1) <;> omega

theorem hubRoom (s : v.Room B base w) : (v.packedHub base).Fits w β₀ ∧ v.rows≤(v.packedHub base).size :=by
  obtain ⟨_,ab,bc,cd,de⟩:=v.ceilings base
  have upper:=bc.trans (cd.trans ((Nat.le_add_right ..).trans de))
  have limit:(v.packedHub base).base+(v.packedHub base).size=α₀:=by dsimp [packedHub,actorBase,Bank.size];omega
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt ((limit.le.trans ab).trans_lt (upper.trans_lt s.space)),limit.le.trans ab⟩,v.rowRoom⟩

theorem actorsRoom (s : v.Room B base w) : DepotRAM.ActorInputs.Room v.socket α₀ H₀ G₀ M₀ w v.raw B.panel B.actors :=by
  obtain ⟨ba,ab,bc,cd,de⟩:=v.ceilings base
  exact ⟨lift (s.prior _ (by simp)) ba,s.panelRows,lift (s.prior _ (by simp)) ba,s.actorRows,
    s.pathsWord,s.keysWord,(bc.trans (cd.trans ((Nat.le_add_right ..).trans de))).trans_lt s.space⟩

theorem rasterRoom (s : v.Room B base w)
    (access : ∀b : Bank,b.Fits w γ₀→v.rows≤b.size→Accessible (rs₀).ports b H₀ G₀ M₀ w γ₀)
    (endFit : (rs₀).ends.Fits w γ₀) (endCapacity : H₀*v.paths≤(rs₀).ends.size) : Raster.Room rs₀ γ₀ H₀ G₀ M₀ w:=by
  obtain ⟨_,_,bc,cd,de⟩:=v.ceilings base
  have high:=cd.trans_lt (((Nat.le_add_right ..).trans de).trans_lt s.space)
  have bankFit (b : Bank) (bound : b.base+b.size≤β₀) : b.Fits w γ₀:=⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt ((bound.trans bc).trans_lt high),bound.trans bc⟩
  obtain ⟨hub,hroom⟩:=v.hubRoom B base s
  exact ⟨access _ (lift hub bc) hroom,endFit,endCapacity,
    fun x j=>bankFit _ (v.ticketRooms base (x,j)).1,fun x j=>(v.ticketRooms base (x,j)).2.2.1,
    fun x j=>bankFit _ (v.ticketRooms base (x,j)).2.1,fun x j=>(v.ticketRooms base (x,j)).2.2.2⟩

set_option maxHeartbeats 1000000 in
theorem any (m : Memory w) (s : v.Room B base w) : (v.phase B base w).Runs m ∧
    ∀a,a<base ∨ v.endAddress base≤a→(v.phase B base w).image m a=m a :=by
  obtain ⟨ba,ab,bc,cd,de⟩:=v.ceilings base
  have co:=cd.trans ((Nat.le_add_right ..).trans de);have high:=co.trans_lt s.space
  let hb:=(v.hubPhase B base w).image m
  let ticket:=(v.pairedPhase B base w).image hb
  let roots:=(v.haloPhase B base w).image ticket
  obtain ⟨r₁,f₁,_⟩:=HubRepeat.any base H₀ G₀ M₀ B.hub m (s.prior _ (by simp)) (ab.trans_lt (bc.trans_lt high))
  obtain ⟨r₂,f₂⟩:=DepotRAM.ActorInputs.all_runs v.socket v.profile v.slots v.raw α₀ B.panel B.actors hb (v.actorsRoom B base s)
  obtain ⟨r₃,access,ef,ec,f₃,_⟩:=DescentScalarHaloProgram.any H₀ G₀ M₀ D₀ B.adjacency β₀ ticket (lift (s.prior _ (by simp)) (ba.trans ab)) s.adjacent s.smallH s.smallD s.smallPaths high
  obtain ⟨r₄,f₄,_⟩:=Raster.any rs₀ v.k v.gain v.slots v.raw v.names H₀ G₀ M₀ γ₀ roots (v.rasterRoom B base s access ef ec) (de.trans_lt s.space)
  let hp := v.hubPhase B base w
  let pp := v.pairedPhase B base w
  let rp := v.haloPhase B base w
  let vp := v.rasterPhase base w
  have run₁ : (hp.seq pp).Runs m := @NativePhase.seq_runs w hp pp m (@r₁) (@r₂)
  have run₂ : ((hp.seq pp).seq rp).Runs m := @NativePhase.seq_runs w (hp.seq pp) rp m (@run₁) (@r₃)
  refine ⟨@NativePhase.seq_runs w ((hp.seq pp).seq rp) vp m (@run₂) (@r₄),?_⟩
  intro a far
  rcases far with lo|hi
  · exact (f₄ _ (.inl (lo.trans_le (ba.trans (ab.trans bc))))).trans ((f₃ _ (.inl (lo.trans_le (ba.trans ab)))).trans ((f₂ _ (.inl (lo.trans_le ba))).trans (f₁ _ (.inl lo))))
  · exact (f₄ _ (.inr (de.trans hi))).trans ((f₃ _ (.inr (co.trans hi))).trans ((f₂ _ (.inr ((bc.trans co).trans hi))).trans (f₁ _ (.inr ((ab.trans (bc.trans co)).trans hi)))))

end
end Hierarchy.DescentOrdinaryVenueIngress.Chart

end OAI
