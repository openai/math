import OAI.Hierarchy.DescentHaloPairRanks

namespace OAI
/-! The scalar banks shared by the ordinary detector and original dated prior header. -/
namespace Hierarchy.DescentOrdinaryDonorRankDirectory
open DescentHaloWalkRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H D w:ℕ} (R:Fin H→Fin D→Option (Fin H))
inductive Field | reverse | localEndpoint | sharedEndpoint deriving DecidableEq

structure Banks extends PairRanks.Banks where
  reverseRank:Bank
  localRank:Bank
  sharedRank:Bank

structure Fits (B:Banks) (out H «P» w:ℕ):Prop extends PairRanks.Fits B.toBanks out H «P» w where
  reverse:B.reverseRank.Fits w out
  localFit:B.localRank.Fits w out
  shared:B.sharedRank.Fits w out
  reverseSize:H*«P»≤B.reverseRank.size
  localSize:H*«P»≤B.localRank.size
  sharedSize:H*(«P»*«P»)≤B.sharedRank.size

local notation "P" => breadth D

/-- The first source page is the deduplicated four-hop directory. The
remaining pages are precisely the ordinary one- and two-walk rank issuances. -/
structure Reads (B:Banks) (m:Memory w):Prop where
  visit:∀v p,m (B.endpoints.base+(Ranks.id v p).val)=(number (Gather.select (Gather.reaching R) v p):Word w)
  prev:∀(v:Fin H)(p q:Fin P),m (B.previous.base+(Ranks.id v (PairRanks.pair p q)).val)=((Ranks.id v p).val:Word w)
  suffix:∀(v:Fin H)(p q:Fin P),m (B.suffix.base+(Ranks.id v (PairRanks.pair p q)).val)=(q.val:Word w)
  offset:∀v:Fin H,m (B.offset.base+v.val)=((v.val*P:ℕ):Word w)
  reverse:∀v p,m (B.reverseRank.base+(Ranks.id v p).val)=(Rebase.value R .rank v p:Word w)
  localValue:∀v p,m (B.localRank.base+(Ranks.id v p).val)=(Ranks.earlier (Rebase.terminal R) v (Rebase.terminal R v p):Word w)
  shared:∀v p q,m (B.sharedRank.base+(Ranks.id v (PairRanks.pair p q)).val)=((PairRanks.ticket (Gather.reaching R) v p q).val:Word w)

end
end Hierarchy.DescentOrdinaryDonorRankDirectory

end OAI
