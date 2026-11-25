import OAI.Computability.BorderVNP.CubeISAOwnedStrictSide
import OAI.Computability.BorderVNP.CubeISALocalRowSpace
import OAI.Computability.BorderVNP.CubeISALocalRowRole
import OAI.Computability.BorderVNP.CubeTeamRowCoverage

/-! # Actual selector and declared words read after an owned scatter -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.OwnedStages Physical Physical.Owned Tally Scatter VPVNP.BurstRAM

variable {w n d blocks b h K s : ℕ} {D : PacketRowData n d blocks b h K s} {A : SideData n d blocks b h}
variable {pub : Arg → Word w} {src : Set ℕ} {r t : Bank w} {m mt : Memory w}

/-- The selector bank seen by the per-role declaration verifier is the selector
tuple that the actual packet scatter consumed. All later singleton and vertex
writes have been accounted for. -/
theorem stored_after_strictSide (ready : SideReady D A pub src r m) (result : SideResult D A src r m t mt)
    (p : Packet n d blocks) (hp : p.1.1 D.axis = D.pair) :
    SelectorRead.Stored (readings mt) (OwnedVertex.bankAt D.base D.stride p) (D.select p) := by
  have positive : 1 < 2^w := by have := ready.singleFit.frameFit; omega
  have hs := scattered_stored D A m positive ready.stride.ge ready.packetsBeforeSingletons p hp
  have before : D.base+(d*d)^(n+1)*2*blocks*D.stride ≤ A.out := ready.packetsBeforeSingletons.trans
    ((Nat.le_add_right _ _).trans ready.singletonsBeforeDirectory)
  intro j
  let params := layout D A.power A.header
  have near := (LocalRow.packetWord_between (l := params) (b := b) (s := s) p j).2
  rw [LocalRow.head_eq] at near
  change D.base+packetIndex p*bankWidth n b h K s+j.val <
    D.base+(d*d)^(n+1)*2*blocks*bankWidth n b h K s at near
  rw [← ready.stride] at near
  have ha : OwnedVertex.bankAt D.base D.stride p+j.val < A.out := near.trans_le before
  have retained := (OwnedVertex.rowImage_frame (blocks := blocks) D.axis D.pair D.high D.base
    D.stride (selectorWidth n K h) A.out (readings (scattered D A m)) (packetTrials n d blocks)).2 _ ha
  exact ((congrFun result.image _).trans retained).trans (hs j)

/-- The actual header and every entry of the decoded declaration table are
resident in the physical input words retained by row scatters. -/
structure CheckImage {w : ℕ} (l : OwnedRowSetup.Layout) (src : Set ℕ) (n actual claimed : ℕ)
    (rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ) (m : Memory w) : Prop where
  actualAt : readings m l.header = actual
  claimedAt : readings m (l.header+1) = claimed
  table : CubeLengths.StoredRows (readings m) claimed rows
  headerWords : l.header ∈ src ∧ l.header+1 ∈ src
  rowWords : ∀ (u v : Fin l.d) (j : Fin (n+1)),
    claimed + (CubeLengths.entryOrder l.d (n+1) ((u,v),j)).val ∈ src

/-- The authentic header and physical declared row survive every stage that
keeps the designated source addresses. -/
theorem CheckImage.transfer {w n actual claimed : ℕ} {l : OwnedRowSetup.Layout} {src : Set ℕ}
    {rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ} {m mt : Memory w}
    (im : CheckImage l src n actual claimed rows m) (keep : ∀ a ∈ src, mt a = m a) :
    CheckImage l src n actual claimed rows mt := by
  refine ⟨(congrArg Fin.val (keep _ im.headerWords.1)).trans im.actualAt,
    (congrArg Fin.val (keep _ im.headerWords.2)).trans im.claimedAt,?_,im.headerWords,im.rowWords⟩
  intro u v j
  exact (congrArg Fin.val (keep _ (im.rowWords u v j))).trans (im.table u v j)

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
