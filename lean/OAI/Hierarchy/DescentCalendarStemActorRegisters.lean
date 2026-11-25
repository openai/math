import OAI.Hierarchy.DescentCalendarPrivatePages
import OAI.Hierarchy.DescentResetNewActorDirectory

namespace OAI
/-! # Original compact actor count, inverse, and occupied flags for the calendar stem -/

namespace Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks

theorem cast_hub {d r c n D R C N : ℕ} (hD : d = D) (hR : r = R)
    (hC : c = C) (hN : n = N) (b : EarlierBanks d r c n) :
    (castTo hD hR hC hN b).oldHub = b.oldHub := by
  subst D
  subst R
  subst C
  subst N
  rfl

end Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook CandidateFront DescentCompiler DescentColonies DescentGL DescentDenseHostOrder
open DescentPackedColony DescentSIMDLookup DescentPackedZip DescentResetNewActorDirectory
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {W : MarkedWorld F d P b}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl) (M : ℕ) (directory : ℕ) (actorBank oldHub : Bank) {bw : ℕ}
    (before : Memory bw)
local notation "H" => S.hostSize i
local notation "cc" => B.terminals.commonDepth
local notation "rosterSize" => (DescentDenseHostOrder.roster B.reset.graph (B.reset.k-cc) (GroupStage.depthBound D n f g)).card
local notation "pitch" => H*rosterSize
local notation "dir" => (⟨directory,H,rosterSize,chunks (2^cc) M⟩ : DescentResetNewActorDirectory.Layout)
local notation "out" => (dir).result actorBank before
local notation "rank₀" => (B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb input.valid.host)
local notation "raw" => B.reset.rawHostRank B.terminals rank₀
local notation "compact" => B.reset.denseHostRank B.terminals rank₀
local notation "used" => Fintype.card B.next.V

/-- The directory produced from the original actor pages, together with the original
old-hub words that lie below its writes. -/
structure StemActorRegisters : Prop where
  counted : out (dir).count.base = (used : Word bw)
  inverseRead : ∀v : B.next.V,out ((dir).inverse.base+((compact) v).val) = (((raw) v).val : Word bw)
  bitmap : ∀j : Fin pitch,out ((dir).flags.base+j.val) = if ∃v,(raw) v=j then 1 else 0
  hubRead : ∀v,out (oldHub.base+(rank₀ v).val) = ((input.placement.hub (B.frame.host.symm v)).toNat : Word bw)
  lowCount : (dir).count.base < (dir).endAddress
  lowInv : (dir).inverse.base+used ≤ (dir).endAddress
  lowMask : (dir).flags.base+pitch ≤ (dir).endAddress
  lowHub : oldHub.base+H ≤ (dir).endAddress
  inverseSize : used ≤ (dir).inverse.size
  hubSize : H ≤ oldHub.size

theorem calendar_stem_actor_registers (positive : 0 < M) (bits : M ≤ bw)
    (actor : ∀l (p : Row H (2^cc) M),
      before (actorBank.base+l.val*(H*chunks (2^cc) M)+(row H (2^cc) M p).val) =
        ((data (Recorded.realActor (reset:=B) (shapes B) (rack B input.valid.host) l) p).val : Word bw))
    (actorFits : actorBank.Fits bw directory) (actorSize : pitch*chunks (2^cc) M ≤ actorBank.size)
    (chunkFit : chunks (2^cc) M ≤ 2^bw) (endFit : (dir).endAddress < 2^bw)
    (hubFits : oldHub.Fits bw directory) (hubSize : H ≤ oldHub.size)
    (hubWords : ∀v : input.V,before (oldHub.base+(input.vertex v).val) = ((input.placement.hub v).toNat : Word bw)) :
    StemActorRegisters B M directory actorBank oldHub before := by
  obtain ⟨_,counted,inverseRead,_,bitmap,frame⟩ :=
    paid_actor_result B input.valid.host directory actorBank before positive bits actor actorFits actorSize chunkFit endFit
  have occupied : used ≤ pitch := by
    let embedding : B.next.V ↪ Fin pitch := raw
    simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding embedding
  have address : used ≤ (dir).inverse.size := occupied.trans (dir).ordered.1
  have baseEnd : directory ≤ (dir).endAddress := Nat.le_add_right ..
  have hubEnd : oldHub.base+H ≤ directory := (Nat.add_le_add_left hubSize _).trans hubFits.2.2
  have bound := (dir).fits endFit
  refine ⟨counted,inverseRead,bitmap,?_,?_,?_,?_,hubEnd.trans baseEnd,address,hubSize⟩
  · intro v
    exact (frame _ (.inl ((Nat.add_lt_add_left (rank₀ v).isLt _).trans_le hubEnd))).trans
      (hubWords (B.frame.host.symm v))
  · exact (Nat.lt_add_of_pos_right bound.2.2.2.1.1).trans_le bound.2.2.2.1.2.2
  · exact (Nat.add_le_add_left address _).trans bound.2.2.2.2.2.2
  · have order := (dir).ordered
    change directory+(dir).pitch+pitch ≤ directory+(4*(dir).pitch+1+4*pitch)
    omega

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
