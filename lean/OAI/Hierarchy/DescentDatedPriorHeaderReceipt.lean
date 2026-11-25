import OAI.Hierarchy.DescentDatedPriorHeaderPaths
import OAI.Hierarchy.DescentOrdinaryRankBanks

namespace OAI
/-! A single measured prior adjacency gives all of the original signed
directory, including repeated visits, reciprocal paths, and unused racks. -/
namespace Hierarchy.DescentDatedAddressBook.PriorHeader
open DescentSixParty.Chronology DescentHaloWalkRAM DescentPackedColony DescentSIMDLookup DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w H G M D:ℕ}
local notation "P"=>breadth D
local notation "N"=>H*P
local notation "L"=>H*(P*P)
local notation "pitch"=>stride H G M D
def rankBanks (H G M D base:ℕ):DescentOrdinaryDonorRankDirectory.Banks:=
  ⟨uniquePairs H G M D base,reverseRank H G M D base,localRank H G M D base,priorRanks H G M D base⟩

variable (base:ℕ) (adj:Bank)
local notation "out"=>image H G M D base adj
local notation "col"=>bank H G M D base
local notation "rk4"=>ranks4 H G M D base
local notation "first"=>duplicates H G M D base
local notation "rev"=>reversals H G M D base
local notation "mix"=>pairs H G M D base
local notation "rk8"=>ranks8 H G M D base
variable (ok:Room adj H G M D base w) (m:Memory w) (R:Fin H→Fin D→Option (Fin H))
  (old:∀(v:Fin H) (j:Fin D),m (adj.base+v.val*D+j.val)=(number (R v j):Word w))
include ok old
local notation "R₄"=>Gather.reaching R
local notation "R₈"=>PairRanks.combined R₄
local notation "steps"=>raw_steps base adj ok m

theorem directory:DescentOrdinaryDonorRankDirectory.Reads R (rankBanks H G M D base) (out m):=by
  have arrays:=pair_words base adj ok m R old
  refine ⟨visits base adj ok m R old,arrays.previous,arrays.suffix,arrays.offset,fun v p=>?_,
    four_rank base adj ok m R old,fun v p q=>?_⟩
  · exact (steps.2.2.2.1 _).trans (Rebase.body_at R rev .rank _ (reversal_room H G M D base adj ok 16 (by decide) (by decide))
      (out m) (reciprocal_words base adj ok m R old) v p)
  · exact octet_rank base adj ok m R old v (PairRanks.pair p q)

end
end Hierarchy.DescentDatedAddressBook.PriorHeader

end OAI
