import OAI.Hierarchy.DescentOrdinaryArchivedInput
import OAI.Hierarchy.DescentOriginalRangeWord

namespace OAI
/-! # The old cells presented to W are the attained dated operand pages -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentDatedPriorOperand DescentDatedAddressBook Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
theorem same_previous_range {w a b : ℕ} {l y : Layout} (same : l=y) (width : a=b)
    (archive : PriorResetArchive) (m : Memory w) (h : 0<l.lanes) (h' : 0<y.lanes)
    (j : ℕ) (f : Fin 3) (x : Fin l.blocks) (x' : Fin y.blocks) (u : Fin l.hosts)
    (u' : Fin y.hosts) (g : Fin l.groups) (g' : Fin y.groups)
    (bx : x.val=x'.val) (hu : u.val=u'.val) (gg : g.val=g'.val) :
    (previousRangeCell archive l a m h j f x u g).val=
      (previousRangeCell archive y b m h' j f x' u' g').val :=by
  subst y
  subst b
  cases Fin.ext bx
  cases Fin.ext hu
  cases Fin.ext gg
  rfl
end
end Hierarchy.DescentRetainedRangeDigits

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
open DescentCompiler DescentColonies DescentDatedPriorOperand DescentDatedAddressBook DescentRetainedRangeDigits
open DescentKernelHistory DescentOperandStateBanks DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} {clock : AtomSchedule} {k i z D wire hist w : ℕ}
    (r : Reached W G q ε clock k i z D wire hist) (arch : BitDescription W)
    (ports : DatePorts) (room : DatePorts.RangeRoom ports r arch)
    (enough : Fintype.card r.V≤ports.operandHosts) (m : Memory w)
    (v : PhysicalOrdinary F P) (A : ArgumentEntry v) (S : A.InputShape v) (floor : ℕ) (matched : A.Match v floor)
    (source : A.previous=ports.rangeLayout) (width : A.previous.size+2=ports.operandBits)
    (radix : k=v.reference.k) (groups : clock.groupCount i=A.clip.venue.groups)
    (population : Fintype.card r.V≤A.clip.venue.hosts)
local notation "positive" => (show 0<A.previous.lanes by rw [source];exact room.positive)
local notation "oldBooks" => (fun pg b=>archivedCell ports.archive A.previous (A.previous.size+2) m positive pg b)

include source width in
/-- Exact numerical identity at every compact host, including every inactive source argument. -/
theorem acquired_prior_range (h : Fin (Fintype.card r.V)) (g : Fin (clock.groupCount i))
    (b : Block k) (j : Fin v.vector.operands) (f : Fin 3) :
    (A.oldInput v S floor matched oldBooks (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f) j)
      (b.cast (congrArg (2^·) radix)) (h.castLE population) (g.cast groups)).val=
    (DatePorts.physicalRangeSource ports r arch room enough m j.val f b h g).val:=by
  have fits : h.val<A.previous.hosts:=by rw [source];exact h.isLt.trans_le enough
  rw [A.old_archived_range v S floor matched ports.archive m positive f j _ _ _ fits]
  exact same_previous_range source width ports.archive m _ _ j.val f _ _ _ _ _ _ rfl rfl rfl
include source width in
/-- The signed date may return any packed row witness. Its observed word uniquely
determines every cell, including the last partially filled chunk. -/
theorem acquired_prior_range_of_reads
    (old : DescentOperandStateBanks.Pages A.previous.operands→Fin A.previous.blocks→
      Fin A.previous.hosts→Fin A.previous.groups→Cell ((A.previous.size+2)*A.previous.nodes))
    (base : A.previousBase=ports.archive.arguments)
    (read : ∀x pg,DescentPackedColony.Reads (DescentDatedPriorOperand.previousBank A.previous A.previousBase x pg)
      (old pg x) A.previous.lanes m)
    (wordFit : (A.previous.size+2)*A.previous.nodes*A.previous.lanes≤w)
    (h : Fin (Fintype.card r.V)) (g : Fin (clock.groupCount i))
    (b : Block k) (j : Fin v.vector.operands) (f : Fin 3) :
    (A.oldInput v S floor matched old (DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f) j)
      (b.cast (congrArg (2^·) radix)) (h.castLE population) (g.cast groups)).val=
    (DatePorts.physicalRangeSource ports r arch room enough m j.val f b h g).val:=by
  have same : old=oldBooks:=by
    funext pg x
    exact (archivedCell_read ports.archive A.previous (A.previous.size+2) m positive pg x (old pg x)
      (base ▸ read x pg) wordFit).symm
  rw [same]
  exact acquired_prior_range r arch ports room enough m v A S floor matched source width radix groups population h g b j f

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI
