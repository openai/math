import OAI.Hierarchy.DescentPackedCensusIngressBill
import OAI.Hierarchy.DescentPackedOrdinaryHardware

namespace OAI
/-! # Code size of the native ordinary program from signed old rows -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentPackedColony DescentStaticWordColumn ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {k D cap N : ℕ} (s : Shape) (chooser : Chooser.Layout) (C : Prepare.Chart k cap)
    (Z : DescentSortedRoster.Chart) (P : Ports D) (wins : Fin (2^k)→Bank) (marked : Fin (2^k)→Fin (2*cap)→Bank)
    (romBase base matcher seats d a K H G M unit w b quota : ℕ)
    (origin out width : ℕ) (bits : Fin N→ℕ) (f : ∀i,Cell (bits i)→ℕ) (source : Fin N→Expr)
set_option quotPrecheck false
local notation "nrows" => H*chunks G M
local notation "intake" => (DescentStaticWordColumn.program w origin (Census.Broadcast.literal H G M) (2*nrows)).seq
  (DescentPackedColumnSum.program w (Census.beginSum origin H G M) out unit M width H G bits f source)
local notation "elect" => chooser.program D k b quota H G M w
local notation "issue_" => Prepared.machine s C Z P wins marked romBase base matcher seats d a K H G M unit w

/-- Counts every printed literal and every scan, including the two stores of
origin IDs and padding masks preceding the raw census. -/
theorem from_old_hardware (work : ℕ) (bounded : ∀i,(source i).work≤work)
    (live : 0<nrows) (payload volume : ℕ)
    (gate : ((1*2^k)+a)*M≤payload/2) (cables : DescentSignedCableCodec.width D cap*M≤payload/2)
    (pages : unit*M≤payload/2) (fits : 2^(payload/2)≤volume) (hosts : H≤volume) (rows : nrows≤volume) :
    CheapCode ((intake).seq ((elect).seq issue_)) ∧
    names ((intake).seq ((elect).seq issue_)) ≤
      (15*(2*nrows+1)+15*(N*2^(unit*M)+1)+15+4*N*(work+6))+
      (4*chooser.ticks D k b quota H G M w+Prepared.namesPerWord k D cap K*volume) := by
  refine ⟨@cheap_seq w _ _ (@cheap_seq w _ _
    (@DescentPackedColumnSum.mount_cheap w origin (Census.Broadcast.literal H G M) (2*nrows))
    (@DescentPackedColumnSum.program_cheap N w (Census.beginSum origin H G M) out unit M width H G bits f source))
    (@ordinary_cheap k D cap s chooser C Z P wins marked romBase base matcher seats d a K H G M unit w b quota),?_⟩
  rw [names_seq]
  exact Nat.add_le_add (Census.hardware N w origin out unit M width H G bits f source work bounded)
    (ordinary_names s chooser C Z P wins marked romBase base matcher seats d a K H G M unit w b quota
      live payload volume gate cables pages fits hosts rows)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
