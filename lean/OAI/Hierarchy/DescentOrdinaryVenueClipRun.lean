import OAI.Hierarchy.DescentOrdinaryVenueIngressRead
import OAI.Hierarchy.DescentOrdinaryVenueClip
import OAI.Hierarchy.DescentOverlapTariff

namespace OAI
/-! # Execute both changes of pitch before the ordinary receiving program -/
namespace Hierarchy.DescentOrdinaryVenueIngress.Clip
open DescentSIMDLookup DescentPackedZip DescentRawCablePanel DescentScalarVenueMask DescentPackedColony DescentHaloWalkRAM
open DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable (c : Clip) (B : Inputs) (base : ℕ) {w : ℕ}
local notation "H₀" => c.venue.hosts
local notation "G₀" => c.venue.groups
local notation "M₀" => c.working
local notation "α₀" => c.actorStart base
local notation "β₀" => c.setupStart base
local notation "Θ" => c.core
local notation "I₀" => c.clipped base B

def transfer (H G A M bits w home : ℕ) (src : Bank) : NativePhase w :=
  ⟨Overlap.program home H G A M bits w src,Overlap.ticks home H G A M bits src,Overlap.result home H G A M bits src,
    cheap_seq (cheap_seq (DescentOrdinaryAtomFieldRAM.ROM.cheap _ _ _ _) (DescentOrdinaryAtomFieldRAM.ROM.cheap _ _ _ _)) (@scan_cheap _ _ _ _)⟩

def panelPhase (w : ℕ):=transfer H₀ G₀ c.panelPitch M₀ c.peerBits w base B.panel
def actorPhase (w : ℕ):=transfer H₀ G₀ c.actorPitch M₀ c.actorBits w α₀ B.actors
def phase (w : ℕ):=((c.panelPhase B base w).seq (c.actorPhase B base w)).seq ((Θ).phase I₀ β₀ w)

structure Room (w : ℕ) : Prop where
  prior : ∀b∈[B.panel,B.actors,B.hub,B.adjacency],b.Fits w base
  oldPanel : Overlap.rows H₀ G₀ c.panelPitch≤B.panel.size
  oldActor : Overlap.rows H₀ G₀ c.actorPitch≤B.actors.size
  hubRows : H₀≤B.hub.size
  adjacency : H₀*c.venue.socket.degree≤B.adjacency.size
  payload : c.payload≤w
  smallH : H₀<2^w
  smallD : c.venue.socket.degree<2^w
  smallPaths : c.venue.paths<2^w
  space : c.fullEnd base<2^w

theorem bounds : base≤α₀ ∧ α₀≤β₀ ∧ β₀≤c.fullEnd base:=by
  obtain ⟨z,p,q,r,e⟩:=(Θ).ceilings β₀
  refine ⟨?_,?_,z.trans (p.trans (q.trans (r.trans ((Nat.le_add_right ..).trans e))))⟩ <;>
    exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))

private theorem grow {b : Bank} {x y w : ℕ} (f : b.Fits w x) (l : x≤y) : b.Fits w y:=⟨f.1,f.2.1,f.2.2.trans l⟩

theorem coreRoom (s : c.Room B base w) : (Θ).Room I₀ β₀ w:=by
  obtain ⟨ba,ab,bc⟩:=c.bounds base
  have f:=Overlap.output_fits base H₀ G₀ c.panelPitch M₀ c.peerBits w ((ab.trans bc).trans_lt s.space)
  have g:=Overlap.output_fits α₀ H₀ G₀ c.actorPitch M₀ c.actorBits w (bc.trans_lt s.space)
  have left : DepotRAM.ActorInputs.bits c.venue.socket≤c.unit:=(le_max_left ..).trans ((le_max_right ..).trans (le_max_left ..))
  have path : DescentSharedCableNames.Packed.bits c.venue.paths≤c.unit:=(Nat.le_succ _).trans ((le_max_left ..).trans ((le_max_right ..).trans ((le_max_right ..).trans (le_max_left ..))))
  have key : DescentSharedCableNames.Packed.bits c.venue.raw≤c.unit:=(le_max_left ..).trans ((le_max_right ..).trans ((le_max_right ..).trans ((le_max_right ..).trans (le_max_left ..))))
  have tight : M₀*c.unit≤w/2:=c.working_fields.2.2.trans (by have room := s.payload; omega)
  refine ⟨?_,f.2.1,g.2.1,s.hubRows,s.adjacency,(Nat.mul_le_mul_left _ (max_le left path)).trans tight,
    (Nat.mul_le_mul_left _ (max_le left key)).trans tight,s.smallH,s.smallD,s.smallPaths,s.space⟩
  intro b mem; simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl
  · exact grow f.1 ab
  · exact g.1
  · exact grow (s.prior _ (by simp [clipped])) (ba.trans ab)
  · exact grow (s.prior _ (by simp [clipped])) (ba.trans ab)

theorem any (m : Memory w) (s : c.Room B base w) : (c.phase B base w).Runs m ∧
    ∀a,a<base ∨ c.fullEnd base≤a→(c.phase B base w).image m a=m a :=by
  obtain ⟨ba,ab,bc⟩:=c.bounds base
  let p:=(c.panelPhase B base w).image m
  let a:=(c.actorPhase B base w).image p
  have cap₁:=Overlap.output_fits base H₀ G₀ c.panelPitch M₀ c.peerBits w ((ab.trans bc).trans_lt s.space)
  have cap₂:=Overlap.output_fits α₀ H₀ G₀ c.actorPitch M₀ c.actorBits w (bc.trans_lt s.space)
  obtain ⟨x,f,_⟩:=Overlap.any base H₀ G₀ c.panelPitch M₀ c.peerBits B.panel m (s.prior _ (by simp)) (cap₁.2.2.trans_lt ((ab.trans bc).trans_lt s.space))
  obtain ⟨y,g,_⟩:=Overlap.any α₀ H₀ G₀ c.actorPitch M₀ c.actorBits B.actors p (grow (s.prior _ (by simp)) ba) (cap₂.2.2.trans_lt (bc.trans_lt s.space))
  obtain ⟨z,h⟩:=(Θ).any I₀ β₀ a (c.coreRoom B base s)
  refine ⟨NativePhase.seq_runs _ _ m (NativePhase.seq_runs _ _ m x y) z,?_⟩
  intro j far;rcases far with lower|upper
  · exact (h _ (.inl (lower.trans_le (ba.trans ab)))).trans ((g _ (.inl (lower.trans_le ba))).trans (f _ (.inl lower)))
  · exact (h _ (.inr upper)).trans ((g _ (.inr (cap₂.2.2.trans (bc.trans upper)))).trans (f _ (.inr (cap₁.2.2.trans (ab.trans (bc.trans upper))))))

theorem issued (m : Memory w) (s : c.Room B base w) (panelPos : 0<c.panelPitch) (actorPos : 0<c.actorPitch)
    (parts : Fin H₀→Fin G₀→DepotRAM.Parts c.venue.socket) (active : Fin H₀→Fin G₀→Cell (1*c.venue.socket.blocks))
    (hubs : Fin H₀→Cell 1) (peer : Fin H₀→Fin c.venue.socket.degree→Option (Fin H₀))
    (panel : Reads B.panel (fun h g=>DepotRAM.combine c.venue.socket (parts h g)) c.panelPitch m)
    (act : Reads B.actors active c.actorPitch m) (one : ∀h : Fin H₀,m (B.hub.base+h.val)=((hubs h).val:Word w))
    (near : ∀h j,m (B.adjacency.base+(h.val*c.venue.socket.degree+j.val))=(number (peer h j):Word w)) :
    let out:=(c.phase B base w).image m
    Reads (c.fieldBank base) (fun h g=>encode (DescentSharedCableNames.Packed.bits c.venue.names) c.actorCount
      («fields» (Gather.reaching peer) ((Θ).values parts active) (fun a _=>hubs a) c.venue.k c.venue.gain c.venue.slots c.venue.names h g)) M₀ out ∧
    Mounted (c.ports base) (DescentSortedRoster.indexed (Gather.reaching peer)) out G₀ M₀ ∧
    (∀src : Bank,src.Fits w (c.fullEnd base)→(Θ).rows ≤ src.size→Accessible (c.ports base) src H₀ G₀ M₀ w (c.fullEnd base)) :=by
  intro out
  obtain ⟨ba,ab,bc⟩:=c.bounds base
  let p:=(c.panelPhase B base w).image m
  let a:=(c.actorPhase B base w).image p
  have cap₁:=Overlap.output_fits base H₀ G₀ c.panelPitch M₀ c.peerBits w ((ab.trans bc).trans_lt s.space)
  have cap₂:=Overlap.output_fits α₀ H₀ G₀ c.actorPitch M₀ c.actorBits w (bc.trans_lt s.space)
  have hi₁:=cap₁.2.2.trans_lt ((ab.trans bc).trans_lt s.space);have hi₂:=cap₂.2.2.trans_lt (bc.trans_lt s.space)
  have lo₁: ∀i,i<base→p i=m i:=fun i early=>(Overlap.any base H₀ G₀ c.panelPitch M₀ c.peerBits B.panel m (s.prior _ (by simp)) hi₁).2.1 i (.inl early)
  have lo₂: ∀i,i<α₀→a i=p i:=fun i early=>(Overlap.any α₀ H₀ G₀ c.actorPitch M₀ c.actorBits B.actors p (grow (s.prior _ (by simp)) ba) hi₂).2.1 i (.inl early)
  have survive {b : Bank} {j : ℕ} (fit:b.Fits w base) (lim:j<b.size) : a (b.base+j)=m (b.base+j):=by
    have lo:= (Nat.add_lt_add_left lim _).trans_le fit.2.2;exact (lo₂ _ (lo.trans_le ba)).trans (lo₁ _ lo)
  have act₁ : Reads B.actors active c.actorPitch p:=fun q=>(lo₁ _ ((Nat.add_lt_add_left ((row H₀ G₀ c.actorPitch q).isLt.trans_le s.oldActor) _).trans_le (s.prior _ (by simp)).2.2)).trans (act q)
  apply (Θ).issued I₀ β₀ a (c.coreRoom B base s) parts active hubs peer
  · intro q
    exact (lo₂ _ ((Nat.add_lt_add_left ((row H₀ G₀ M₀ q).isLt.trans_le cap₁.2.1) _).trans_le cap₁.1.2.2)).trans (Overlap.read base B.panel m _ panelPos (s.prior _ (by simp)) s.oldPanel panel hi₁ q)
  · exact Overlap.read α₀ B.actors p _ actorPos (grow (s.prior _ (by simp)) ba) s.oldActor act₁ hi₂
  · intro h;exact (survive (s.prior _ (by simp)) (h.isLt.trans_le s.hubRows)).trans (one h)
  · intro h j
    have lim : h.val*c.venue.socket.degree+j.val<H₀*c.venue.socket.degree:=(Nat.add_lt_add_left j.isLt _).trans_le (by
      change h.val*c.venue.socket.degree+c.venue.socket.degree≤H₀*c.venue.socket.degree
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ h.isLt)
    exact (survive (s.prior _ (by simp)) (lim.trans_le s.adjacency)).trans (near h j)

end
end Hierarchy.DescentOrdinaryVenueIngress.Clip

end OAI
