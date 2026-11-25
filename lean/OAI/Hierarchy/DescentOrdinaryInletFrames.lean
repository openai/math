import OAI.Hierarchy.DescentOrdinaryAfterSigned

namespace OAI
/-! # Readable intermediate memories of the native ordinary argument entrance -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
open DescentDatedPriorOperand DescentOrdinaryAtomFieldRAM DescentPackedColony DescentSIMDLookup
open ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (A : ArgumentEntry v)
variable (floor : ℕ) {w : ℕ} (m : Memory w)

def clippedTape := (A.clip.phase A.venue (v.signedEnd floor) w).image m
def priorTape := (DescentOrdinaryPriorPad.phase A.previous A.clip.venue.hosts A.clip.working
  (A.priorStart v floor) A.previousBase w).image (A.clippedTape v floor m)
def roleTape := ((A.roleLayout v).phase (A.roleStart v floor) A.role w).image (A.priorTape v floor m)
def chipTape := ((A.chip v).phase (A.chipStart v floor) (A.chipSource v floor) w).image (A.roleTape v floor m)

structure InletFrames : Prop where
  clipped (i : ℕ) : i<v.signedEnd floor → A.clippedTape v floor m i=m i
  old (i : ℕ) : i<A.priorStart v floor → A.priorTape v floor m i=A.clippedTape v floor m i
  role (i : ℕ) : i<A.roleStart v floor → A.roleTape v floor m i=A.priorTape v floor m i
  chip (i : ℕ) : i<A.chipStart v floor → A.chipTape v floor m i=A.roleTape v floor m i
  count (i : ℕ) : i<A.populationBase v floor → (A.inlet v floor w).image m i=A.chipTape v floor m i

theorem inlet_frames (safe : A.Room v floor w) : A.InletFrames v floor m :=by
  obtain ⟨_,_,labels,chip,pop⟩:=A.inlet_order v floor
  have pc:=pop.trans_lt safe.ceiling
  have cc:=chip.trans_lt pc
  have lc:=labels.trans_lt cc
  exact ⟨fun i hi=>(A.clip.any A.venue (v.signedEnd floor) m safe.venue).2 i (.inl hi),
    fun i hi=>(DescentOrdinaryPriorPad.any A.previous A.clip.venue.hosts A.clip.working (A.priorStart v floor) A.previousBase
      (A.clippedTape v floor m) safe.prior lc).2 i (.inl hi),
    fun i hi=>((A.roleLayout v).any (A.roleStart v floor) A.role (A.priorTape v floor m) safe.roles cc).2 i (.inl hi),
    fun i hi=>((A.chip v).framed (A.chipStart v floor) (A.chipSource v floor) (A.roleTape v floor m)
      safe.chipLow safe.chipRows safe.chipBits pc).2 i (.inl hi),
    fun i hi=>((A.population v floor).any (A.ports v floor) (A.labels v floor)
      (A.chipTape v floor m) safe.walk safe.ceiling).2.2.2 i (.inl hi)⟩

/-- An entire packed bank survives a later physical cut as long as the last
possible packed row is below the cut. -/
theorem reads_through {h g b M cut : ℕ} {reg : Bank} {val : Fin h→Fin g→Cell b}
    {before after : Memory w} (held : Reads reg val M before) (end_ : reg.base+reg.size≤cut)
    (size : h*chunks g M≤reg.size) (frame : ∀i,i<cut → after i=before i) : Reads reg val M after :=by
  intro p
  exact (frame _ ((Nat.add_lt_add_left ((row h g M p).isLt.trans_le size) _).trans_le end_)).trans (held p)

theorem prior_final (safe : A.Room v floor w) (x : Fin A.previous.blocks)
    (p : DescentOperandStateBanks.Pages A.previous.operands)
    (value : Fin A.previous.hosts → Fin A.previous.groups → Cell (DescentOrdinaryPriorRetile.digits A.previous))
    (nonempty : 0<A.previous.lanes)
    (early : (previousBank A.previous A.previousBase x p).Fits w (v.signedEnd floor))
    (held : Reads (previousBank A.previous A.previousBase x p) value A.previous.lanes m) :
    Reads (DescentOrdinaryPriorPad.bank A.previous A.clip.venue.hosts A.clip.working (A.priorStart v floor) x p)
      (DescentOrdinaryPriorPad.extend A.clip.venue.hosts value) A.clip.working
      ((A.inlet v floor w).image m) :=by
  let frames:=A.inlet_frames v floor m safe
  obtain ⟨_,_,role,chip,pop⟩:=A.inlet_order v floor
  have stop:=role.trans_lt (chip.trans_lt (pop.trans_lt safe.ceiling))
  have size : A.previous.rows≤(previousBank A.previous A.previousBase x p).size :=
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have input:=reads_through held early.2.2 size frames.clipped
  have rows:=DescentOrdinaryPriorPad.reads A.previous A.clip.venue.hosts A.clip.working (A.priorStart v floor) A.previousBase
    (A.clippedTape v floor m) safe.prior stop x p value nonempty input
  have placed:=DescentOrdinaryPriorPad.placed A.previous A.clip.venue.hosts A.clip.working (A.priorStart v floor) stop x p
  refine reads_through rows placed.1.2.2 placed.2 ?_
  intro i hi
  exact (frames.count i (hi.trans_le (role.trans chip))).trans ((frames.chip i (hi.trans_le role)).trans (frames.role i hi))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI
