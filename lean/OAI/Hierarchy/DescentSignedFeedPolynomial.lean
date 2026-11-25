import OAI.Hierarchy.DescentSignedFeedTariff

namespace OAI
/-! # A uniform polynomial for the signed executor's instructions per packed word -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentHaloWalkRAM

private def uniform (n : ℕ) : SignedExtent where
  blocks := n
  priorHosts := 0
  hosts := 0
  groups := 0
  lanes := 0
  degree := n
  residentSlots := n
  lowSites := n
  tickets := n
  cap := n
  fieldBits := n

/-- All host and group cardinalities are already charged by the physical volume.
Only local ranks, candidate multiplicities and expression work enter this coefficient. -/
theorem feedFactor_polynomial (s : SignedExtent) (K : ℕ) :
    s.feedFactor K ≤ 10^12*(1+s.blocks+s.degree+s.residentSlots+s.lowSites+s.cap+K)^48 := by
  let n:=s.blocks+s.degree+s.residentSlots+s.lowSites+s.cap+K
  have blocks : s.blocks≤n:=by dsimp [n];omega
  have deg : s.degree≤n:=by dsimp [n];omega
  have slots : s.residentSlots≤n:=by dsimp [n];omega
  have lows : s.lowSites≤n:=by dsimp [n];omega
  have cap : s.cap≤n:=by dsimp [n];omega
  have snippets : K≤n:=by dsimp [n];omega
  let t:=uniform n
  have paths : s.reach≤t.reach:=by
    change (s.degree+1)^4≤(n+1)^4
    gcongr
  have cc : s.candidates≤t.candidates:=Nat.mul_le_mul paths slots
  change s.blocks ≤ t.blocks at blocks
  change s.lowSites ≤ t.lowSites at lows
  change s.cap ≤ t.cap at cap
  have jobs : s.jobsLocal≤t.jobsLocal:=Nat.mul_le_mul blocks cc
  have compare : s.jobsCompare≤t.jobsCompare:=by unfold jobsCompare;gcongr
  have key : s.oldKey≤t.oldKey:=by unfold oldKey;gcongr
  have routes : s.routeTotal ≤ t.routeTotal := key
  have peerKindsBound : s.peerKinds ≤ t.peerKinds := Nat.mul_le_mul (Nat.mul_le_mul paths paths) lows
  have peer : s.shortPeerKinds≤t.shortPeerKinds:=by unfold shortPeerKinds;gcongr
  have dir : s.rankDirectoryFactor≤t.rankDirectoryFactor:=by unfold rankDirectoryFactor;gcongr
  have index : s.signedIndexFactor≤t.signedIndexFactor:=by unfold signedIndexFactor;gcongr
  have reverse_ : s.reverseInstallFactor≤t.reverseInstallFactor:=by unfold reverseInstallFactor;gcongr
  have peerSelect : s.peerSelectionFactor≤t.peerSelectionFactor:=by unfold peerSelectionFactor;gcongr
  have peerHeader : s.peerDirectoryFactor≤t.peerDirectoryFactor:=by unfold peerDirectoryFactor;gcongr
  have prep : s.preparationFactor≤t.preparationFactor:=by unfold preparationFactor;gcongr
  have limit : s.prepLimit K≤t.prepLimit n:=by
    unfold prepLimit rankCost donorCost routeCost queryCost directoryCost
    gcongr
  have pref : s.prefixFactor K≤t.prefixFactor n:=by unfold prefixFactor peerInstallFactor;gcongr
  have header : s.headerLimit K≤t.headerLimit n:=by unfold headerLimit;gcongr
  have ranks : s.rankExpr K≤t.rankExpr n:=by unfold rankExpr gatedLimit;gcongr
  have outputs : s.outputExpr K≤t.outputExpr n:=by unfold outputExpr;gcongr
  have rc : s.rankColumns≤t.rankColumns:=by unfold rankColumns;gcongr
  have oc : s.outputColumns≤t.outputColumns:=by unfold outputColumns;gcongr
  have clock : s.feedClockFactor K≤t.feedClockFactor n:=by unfold feedClockFactor;gcongr
  have text_ : s.feedTextFactor K≤t.feedTextFactor n:=by unfold feedTextFactor;gcongr
  have bound : s.feedFactor K≤t.feedFactor n:=by unfold feedFactor;gcongr
  have normalized : t.feedFactor n≤10^12*(1+n)^48:=by
    dsimp only [t,feedFactor,feedClockFactor,feedTextFactor,prefixFactor,prepLimit,rankCost,donorCost,
      routeCost,queryCost,directoryCost,rankDirectoryFactor,peerInstallFactor,preparationFactor,
      signedIndexFactor,reverseInstallFactor,peerSelectionFactor,peerDirectoryFactor,rankColumns,outputColumns,
      rankExpr,gatedLimit,outputExpr,headerLimit,jobsCompare,jobsLocal,candidates,oldKey,routeTotal,peerKinds,
      shortPeerKinds,reach,breadth,uniform]
    ring_nf
    omega
  simpa only [n,Nat.add_assoc] using bound.trans normalized

end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
