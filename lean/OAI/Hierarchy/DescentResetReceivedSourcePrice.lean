import OAI.Hierarchy.DescentResetReceivedTariff
import OAI.Hierarchy.DescentFrontEarlierRoot

namespace OAI
/-! The concrete signed, rotor, stem and peer expression costs in an issued reset scene. -/
namespace Hierarchy.DescentResetPeerUnionRAM.PeerCatalog
open DescentResetLocalRoster
noncomputable section
theorem terms_work (L : RawTables.Layout) (A : DescentContactPreROM.Layout) (B : Banks A)
    (j : Fin (Axes.rows A.donors A.sockets (privateAxis L A))) (p : Fin (DescentSIMDLookup.chunks A.groups A.batch)) :
    ((terms L A B).all j p).work≤128 := by
  classical
  obtain ⟨i,rfl⟩:=(Axes.order A.donors A.sockets (privateAxis L A)).surjective j
  rw [Axes.Fields.all_at]
  rcases i with f|s|⟨left,right⟩|slot
  · exact ((DescentResetStemPeerChip.data_work ..).le.trans (show _≤128 from of_decide_eq_true rfl))
  · exact of_decide_eq_true rfl
  · exact of_decide_eq_true rfl
  · change ((terms L A B).privateEdge slot p).work ≤ 128
    dsimp only [terms]
    split <;> exact of_decide_eq_true rfl
end
end Hierarchy.DescentResetPeerUnionRAM.PeerCatalog

namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSixParty DescentCompiler DescentDenseHostOrder DescentSIMDLookup DescentPackedColony
open DescentResetPeerUnionRAM DescentResetStemPackedIssue DescentFallbackPeriod DescentResetLocalRoster
open ProtocolRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
variable {n h : ℕ} (S : AtomSchedule) (board : NonlinearExpanders.Graph n h)
    (k tail age degree f g receiverBatch nextBatch rootField metaBits C packet : ℕ) (calendar : List ℕ)
local notation "A" => setupFront S board k tail age degree f g receiverBatch nextBatch rootField metaBits C packet calendar
local notation "height" => GroupStage.depthBound degree n f g
variable (floor : ℕ) (early : EarlierBanks degree k ((calendar.take age).prod*256) n) (flags count inverse : Bank)
local notation "org" => calendarOriginals S board k tail age degree f g receiverBatch nextBatch rootField metaBits C packet calendar floor early
local notation "s" => (A).fromOriginals floor (org) flags count inverse

def sourceLimit (palette donor : ℕ) := 128+DescentResetTrunkScalar.tableWork+(22+8*palette)+donor

private theorem source_limit_bounds (x y u : ℕ) :
    let z := 128+x+(22+8*y)+u
    45 ≤ z ∧ 128 ≤ z ∧ x ≤ z ∧ u ≤ z ∧ 22+8*y ≤ z := by
  dsimp only; omega

theorem original_price (U : ℕ) (matrix : ∀j,(early.donor.board j).work≤U)
    (host : early.donor.host.work≤U) (ones : early.donor.ones.work≤U) :
    (A).OperandPrice (s) (sourceLimit (roster board k height).card U) := by
  let limit:=sourceLimit (roster board k height).card U
  obtain ⟨small,read,trunk,earlier,bound⟩ :=
    source_limit_bounds DescentResetTrunkScalar.tableWork (roster board k height).card U
  have stem (q : Fin (DescentResetStemPackedIssue.count (2^k) ((calendar.take age).prod*256))) (i : Fin (degree+2)) :
      (operands early.ports early.window (S.hostSize age) q i).work ≤ limit :=
    (DescentResetStemKey.readers_work ..).trans small
  have masked:=DescentResetStemMaskedPorts.work
    ⟨inverse,(A).parent floor,(A).rawNeighborBank floor,early.oldHub⟩ count (A).peer.oldHosts ((A).signedTemplate (org).evidence)
  refine ⟨stem,fun j=>(matrix j).trans earlier,host.trans earlier,ones.trans earlier,
    fun j=>(matrix _).trans earlier,fun j p=>(PeerCatalog.terms_work ..).trans read,?_,stem,?_⟩
  · exact (ClosedReset.Window.raw_trunk_work ..).le.trans trunk
  · exact ⟨masked.here.trans bound,fun j=>(masked.near j).trans bound,fun j=>(masked.src j).trans bound,
      fun j=>(masked.dst j).trans bound,fun j=>(masked.hub j).trans bound⟩

open DescentFallbackPeriod.Projected DescentResetGates DescentSharedBookScan
namespace EarlierBanks
variable {D r cap₀ N h₁ dim width c hosts G K R M l t field Ht w : ℕ}
  (a : Receiver D cap₀ N dim r c hosts G K R M h₁ l t field Ht w)
  (book : RootBook dim r D (2^r) cap₀ field)
  (orig : RootSources D (2^r) cap₀) (oldId oldHub : Bank)
  (dir : DescentResetNewActorDirectory.Layout) (scene : Bank)
local notation "e" => fromRoot a book orig oldId oldHub dir scene

/-- Sender terms are the original ordered and reserved rotor rows, plus a constant-size
read from the real rank header. The roster, ticket and issued hub reads are priced here. -/
theorem sender_limit (U : ℕ) (matrix : ∀j,(orig.matrixRow hosts j).work≤U) :
    (∀j,((e).donor.board j).work≤U+64) ∧
    (e).donor.host.work≤U+64 ∧ (e).donor.ones.work≤U+64 := by
  refine ⟨?_,(show _≤64 from of_decide_eq_true rfl).trans (Nat.le_add_left ..),(show _≤64 from of_decide_eq_true rfl).trans (Nat.le_add_left ..)⟩
  intro j
  obtain ⟨branch,rfl⟩ := finSumFinEquiv.surjective j
  cases branch with
  | inl i =>
    obtain ⟨field,rfl⟩ := DescentRotorWindowArchive.ix.surjective i
    have m := matrix (DescentRotorWindowArchive.ix field)
    simp only [fromRoot,RootSources.senderPrior,RootSources.matrixRow,
      Equiv.symm_apply_apply,Sum.elim_inl] at m ⊢
    rcases field with (((a|⟨b,c⟩)|⟨d0,e0⟩)|(⟨f,g⟩|⟨i,j,k⟩)) <;>
      exact m.trans (Nat.le_add_right ..)
  | inr i =>
    simp only [fromRoot,RootSources.senderPrior,Equiv.symm_apply_apply,Sum.elim_inr]
    exact (show _≤64 from of_decide_eq_true rfl).trans (Nat.le_add_left ..)

end EarlierBanks
end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
