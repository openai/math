import OAI.Hierarchy.DescentContactLateMass
import OAI.Hierarchy.DescentResetSignedHaloLate
import OAI.Hierarchy.DescentContactPostTrunkPitch

namespace OAI
/-! # The complete post-trunk direct contact count and complementary old halo -/
namespace Hierarchy.DescentContactMaskShape
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentContactDonorFront
open DescentResetSignedHaloMatrix DescentPackedChildNeighbor.SIMD DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (A : Shape) (donorStart first : ℕ) {w : ℕ}
variable (u : DescentContactSenderDate.Prior A.degree A.lows A.cap A.n A.residual)
local notation "C" => A.halo donorStart u.routes.roster
local notation "R" => massEnd A first
local notation "H" => A.hosts
local notation "G" => A.groups
local notation "M" => A.batch
local notation "D" => A.degree

def period (w : ℕ):=(program A donorStart first w).seq (Right.program (C) R w)
def result (m : Memory w):=Right.memory (C) R (memory A donorStart first m)
def clock:=ticks A donorStart first+Right.ticks (C)
def rightPort (src : Expr):=Right.port (C) R src

theorem extent : Right.high (C) R=endAddress A first:=rfl
theorem mass_bottom : first≤ massEnd A first:=by
  have h:=(date A first).ordered (donors A+1) A.fieldBits
  exact (Nat.le_add_right ..).trans (h.1.trans ((Nat.le_add_right ..).trans (h.2.1.trans h.2.2)))

variable (ordered : A.endAddress donorStart≤first) (r : A.Space donorStart u w) (room : endAddress A first<2^w)
include ordered in
private theorem initial_before : A.idBase donorStart≤first :=
  (A.ordered donorStart).2.1.trans ((A.ordered donorStart).2.2.trans ordered)

include ordered r room in
theorem period_any (m : Memory w) :
    (period A donorStart first u w).Exec m (result A donorStart first u m) (clock A donorStart first u) ∧
    CheapCode (period A donorStart first u w) ∧
    ∀addr,addr<first ∨ endAddress A first≤addr→ result A donorStart first u m addr=m addr:=by
  have low:=mass_bottom A first
  have high : R≤endAddress A first:=Nat.le_add_right ..
  have first_:=any A donorStart first u (initial_before A donorStart first ordered) r (high.trans_lt room) m
  have after:=Right.any (C) R room (memory A donorStart first m)
  exact ⟨Procedure.Exec.then first_.1 after.1,cheap_seq first_.2.1 after.2.1,fun a pos=>
    (after.2.2 a (pos.imp (fun h=>h.trans_le low) id)).trans
      (first_.2.2 a (pos.imp id (fun h=>high.trans h)))⟩

def native : NativePhase w:=⟨period A donorStart first u w,clock A donorStart first u,result A donorStart first u,
  (period_any A donorStart first u ordered r room (fun _=>0)).2.1⟩

theorem period_priced :
    clock A donorStart first u≤DescentContactSenderMass.Date.clockBound (A.sender donorStart) first+(4+10*directionSize A) ∧
    DescentStaticWordColumn.names (period A donorStart first u w)≤
      DescentContactSenderMass.Date.nameBound (A.sender donorStart) first+15*(directionSize A+1):=by
  have cost:=tariff (w:=w) A donorStart first
  constructor
  · exact Nat.add_le_add_right cost.1 _
  · unfold period Right.program DescentOrdinaryAtomFieldRAM.ROM.mount
    rw [DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_mount]
    exact Nat.add_le_add_right cost.2 _

include ordered r in
theorem right_source (postTrunk initial : Memory w) (p : Fin H→Fin D→Option (Fin H)) (mounted : Mounted u.routes p initial G M)
    (wide : D+2<2^A.cargoBits) (space : endAddress A first+H*chunks G M<2^w)
    (retained : ∀z,z<A.endAddress donorStart→postTrunk z=A.memory donorStart u initial z)
    (src : Expr) (x : Fin H→Fin G→Cell A.fieldBits) (fit : src.Fits w first) (seen : Source src x M postTrunk) :
    (rightPort A donorStart first u src).Fits w (endAddress A first) ∧
      Source (rightPort A donorStart first u src)
        (fun h g=>lookup (short (b:=A.cargoBits) p id h)
          (Right.askedField D A.cap A.fieldBits A.queryBits (x h g) 0) (List.finRange (D+1))) M
        (result A donorStart first u postTrunk):=by
  obtain ⟨_,counted,names,edges⟩:=A.identity_roster donorStart u r initial p mounted
  have haloRoom:=A.haloFits donorStart u r
  have archive:=(C).stored haloRoom (A.idImage donorStart u initial) p id le_rfl
    (DescentResetOriginalSlots.rows_le H) wide counted names edges
  have finish : R<2^w:=(Nat.le_add_right ..).trans_lt ((Nat.le_add_right ..).trans_lt space)
  have passed:=(any A donorStart first u (initial_before A donorStart first ordered) r finish postTrunk).2.2
  have low:=mass_bottom A first
  refine Right.posted (C) R haloRoom (by rw [A.halo_end];exact ordered.trans low) space
    (short (b:=A.cargoBits) p id) archive ?_ src x (ProtocolRAMGeneratedWrite.fits_mono _ low fit) ?_
  · intro z hz
    rw [A.halo_end] at hz
    exact (passed z (.inl (hz.trans_le ordered))).trans (retained z hz)
  · intro q
    exact (eval_below _ _ postTrunk _ fit (fun z hz=>passed z (.inl hz))).trans (seen q)

end
end Hierarchy.DescentContactMaskShape

end OAI
