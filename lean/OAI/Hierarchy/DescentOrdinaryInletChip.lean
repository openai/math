import OAI.Hierarchy.DescentOrdinaryInletFrames

namespace OAI
/-! # Actual donor chip and primitive labels at the ordinary argument entrance -/
namespace Hierarchy
open DescentSIMDLookup DescentRawCablePanel DescentPackedColony DescentPacking.PackedMatch.Local
open DescentColonies.SplitRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

namespace DescentOrdinaryVenueIngress.Clip
variable (c : Clip) (B : Inputs) (base : ℕ) {w : ℕ}

/-- The first conversion's physical panel survives the actor conversion and the full venue scan. -/
theorem panel_held (m : Memory w) (s : c.Room B base w) (positive : 0<c.panelPitch)
    (v : Fin c.venue.hosts → Fin c.venue.groups → Cell c.peerBits) (read : Reads B.panel v c.panelPitch m) :
    Reads (c.clipped base B).panel v c.working ((c.phase B base w).image m) :=by
  obtain ⟨ba,ab,bc⟩:=c.bounds base
  let p:=(c.panelPhase B base w).image m
  let a:=(c.actorPhase B base w).image p
  have cap:=Overlap.output_fits base c.venue.hosts c.venue.groups c.panelPitch c.working c.peerBits w ((ab.trans bc).trans_lt s.space)
  have acap:=Overlap.output_fits (c.actorStart base) c.venue.hosts c.venue.groups c.actorPitch c.working c.actorBits w (bc.trans_lt s.space)
  have early: B.actors.Fits w (c.actorStart base) :=
    let held:=s.prior B.actors (by simp)
    ⟨held.1,held.2.1,held.2.2.trans ba⟩
  have af:=Overlap.any (c.actorStart base) c.venue.hosts c.venue.groups c.actorPitch c.working c.actorBits B.actors p
    early (acap.2.2.trans_lt (bc.trans_lt s.space))
  have cf:=c.core.any (c.clipped base B) (c.setupStart base) a (c.coreRoom B base s)
  have panel : Reads (c.clipped base B).panel v c.working p :=
    Overlap.read base B.panel m v positive (s.prior _ (by simp)) s.oldPanel read
      (cap.2.2.trans_lt ((ab.trans bc).trans_lt s.space))
  apply DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry.reads_through panel cap.1.2.2 cap.2.1
  intro i lo
  exact (cf.2 i (.inl (lo.trans_le ab))).trans (af.2.1 i (.inl lo))

end DescentOrdinaryVenueIngress.Clip

namespace DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (A : ArgumentEntry v)
variable (floor : ℕ) {w : ℕ} (m : Memory w)

theorem role_before_count (safe : A.Room v floor w) (x : Fin A.previous.blocks)
    (value : Fin A.previous.hosts → Fin A.clip.venue.groups → Cell (A.roleLayout v).bits)
    (positive : 0<A.rolePitch) (early : (A.role x).base+(A.role x).size≤v.signedEnd floor)
    (capacity : A.previous.hosts*chunks A.clip.venue.groups A.rolePitch≤(A.role x).size)
    (held : Reads (A.role x) value A.rolePitch m) :
    Reads (A.labels v floor x) (DescentOrdinaryHostPad.extend A.clip.venue.hosts value) A.clip.working (A.chipTape v floor m) :=by
  let frames:=A.inlet_frames v floor m safe
  obtain ⟨start,_,_,lower,last⟩:=A.inlet_order v floor
  have stop:=lower.trans_lt (last.trans_lt safe.ceiling)
  have old:=reads_through held early capacity (fun i lo=>(frames.old i (lo.trans_le start)).trans (frames.clipped i lo))
  have actual:=(A.roleLayout v).reads (A.roleStart v floor) A.role (A.priorTape v floor m)
    safe.roles stop x value positive capacity old
  have placed:=(A.roleLayout v).placed (A.roleStart v floor) stop x
  exact reads_through actual placed.1.2.2 placed.2 frames.chip

theorem chip_final (safe : A.Room v floor w) (positive : 0<A.clip.panelPitch)
    (parts : Fin A.clip.venue.hosts → Fin A.clip.venue.groups → DepotRAM.Parts A.clip.venue.socket)
    (held : Reads A.venue.panel (fun h g=>DepotRAM.combine A.clip.venue.socket (parts h g)) A.clip.panelPitch m) :
    Reads (A.chipBank v floor) (fun h g=>DepotRAM.chip A.clip.venue.socket A.clip.venue.socket.cap
      A.clip.venue.profile v.gadget.b A.clip.venue.slots (parts h g)) A.clip.working ((A.inlet v floor w).image m) :=by
  let c:=A.clip
  let frames:=A.inlet_frames v floor m safe
  obtain ⟨_,toRole,_,_,last⟩:=A.inlet_order v floor
  obtain ⟨_,ab,bc⟩:=c.bounds (v.signedEnd floor)
  have placed:=Overlap.output_fits (v.signedEnd floor) c.venue.hosts c.venue.groups c.panelPitch c.working c.peerBits w
    ((ab.trans bc).trans_lt safe.venue.space)
  have panel:=c.panel_held A.venue (v.signedEnd floor) m safe.venue positive _ held
  have current:=reads_through panel (placed.1.2.2.trans (ab.trans bc)) placed.2.1
    (fun i lo=>(frames.role i (lo.trans_le toRole)).trans (frames.old i lo))
  have chip:=(A.chip v).reads (A.chipStart v floor) (A.chipSource v floor) (A.roleTape v floor m)
    safe.chipLow safe.chipRows safe.chipBits (last.trans_lt safe.ceiling) parts current
  have capacity : (A.chip v).rows≤(A.chipBank v floor).size :=
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  exact reads_through chip (show (A.chipBank v floor).base+(A.chipBank v floor).size≤A.populationBase v floor from le_rfl)
    capacity frames.count

end DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
end
end Hierarchy

end OAI
