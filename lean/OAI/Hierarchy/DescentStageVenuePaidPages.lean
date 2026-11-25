import OAI.Hierarchy.DescentStageVenueAny

namespace OAI
/-! # The original packed paid counts on both sides of venue publication -/
namespace Hierarchy.DescentSixParty.StageVenueTail
open DescentCompiler DescentPackedColony DescentColonies DescentSIMDLookup
open DescentPacking.PackedMatch.Local.Stage ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P:Type} [Field F] {u:ℕ} {bits:P→ℕ} {W:MarkedWorld F u P bits}
    {G:PoweredGadget F} {q ε:ℝ} {S:AtomSchedule} {k age z D wire hist H w:ℕ}

def paidCounts (B:Sources) (r:Reached W G q ε S k age z D wire hist)
    (wide:Fintype.card r.V≤H) (countBits lanes:ℕ) (m:Memory w) : Prop :=
  ∀x:Block k, Reads (B.paid x.val)
    (fun h g=> Census.count r.placement (Equiv.refl _) (r.vertex.trans (Fin.castLEEmb wide)) countBits h g x)
    lanes m

theorem Date.paid_counts_after (d:Date) (B:Sources)
    (r:Reached W G q ε S d.k age z D wire hist) (wide:Fintype.card r.V≤d.hosts)
    (groups:S.groupCount age=d.groups) (base:ℕ) (m:Memory w) (room:d.Space B base w)
    (paid:paidCounts B r wide d.paidBits d.paidLanes m) :
    paidCounts B r wide d.paidBits d.paidLanes ((d.phase B base w).image m):=by
  intro x p
  have used: (row d.hosts (S.groupCount age) d.paidLanes p).val < (B.paid x.val).size :=
    (row d.hosts (S.groupCount age) d.paidLanes p).isLt.trans_le (by rw [groups];exact (room.paid x).2)
  have below:= (Nat.add_lt_add_left used (B.paid x.val).base).trans_le (room.paid x).1.2.2
  exact ((d.any B base m room).2 _ (.inl below)).trans (paid x p)

end
end Hierarchy.DescentSixParty.StageVenueTail

end OAI
