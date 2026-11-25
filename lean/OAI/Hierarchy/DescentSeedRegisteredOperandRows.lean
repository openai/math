import OAI.Hierarchy.DescentSeedTokenRun
import OAI.Hierarchy.DescentSeedCompleteImage
import OAI.Hierarchy.DescentSeedNativeReadout
import OAI.Hierarchy.DescentSeedRegisterPorts
import OAI.Hierarchy.DescentArchiveRegisterCoordinates
import OAI.Hierarchy.DescentPreviousOperandLayout

namespace OAI
/-! # Every initial operand page in the original, fully loaded memory -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler Catalyst DescentInitialHost DescentPackedSeed DescentDatedSeedStartup
open DescentSeedRoot DescentSeedInitialTable DescentColonies DescentDyadicSpan
open DescentDatedSeedStartup.Input DescentDatedPriorOperand DescentOperandStateBanks
open DescentPackedColony DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {S : AtomSchedule} (G : PoweredGadget F) (op : RotorSpec)
    {k cp p H : ℕ} (X : Approximation F cp p)
    (digits : Fin S.copies≃Fin (S.groupCount 0)×Block k)
    (publicWide : Fintype.card (Vertex X)≤H) (l : DescentDatedSeedStartup.Layout) (header payload Z : ℕ)
local notation "g₀" => S.groupCount 0
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => DescentDatedSeedStartup.endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "Q" => nodeArities X publicWide l
local notation "finish" => (chart).seedEnd top
local notation "lanes" => DescentDatedSeedStartup.Primitive.paletteLanes G op l.seedWidth Z payload k
local notation "limit" => DescentDatedSeedStartup.Primitive.initialEnd X S.copies l.seedWidth payload k H g₀ lanes finish
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
local notation "ports" => initial G op X S.copies l k H g₀ payload Z
local notation "final" => completeImage G op X digits publicWide l header payload Z
local notation "ob" => operandBase X l H g₀
local notation "db" => directoryBase X l H g₀ k
local notation "argBase" => Seed.Physical.bankStart X ob k g₀ l.operandLanes
local notation "L" => (ports).rangeLayout

/-- The original finite seed loader writes all seven pages, before its header clear, initial
metadata program and primitive role publication. All three later instructions preserve these rows. -/
theorem seed_operand_cells {w : ℕ} (m : Memory w) (fields : l.operandBits*l.operandLanes≤w)
    (early : header<l.base) (sourceSpace : publicWords X+DescentDyadicSpan.span jobs≤finish)
    (live : 0<lanes) (machine : payload≤w) (space : limit<2^w)
    (f : DescentOperandStateBanks.Field) (arg : Fin (ports).argumentsPerNode) (x : Fin (L).blocks) :
    Reads (previousBank L (ports).archive.arguments x (page f arg))
      (Seed.Physical.value X hs (Equiv.refl _) digits l.groupsPerNode l.operandBits 1 arg.val f x)
      (L).lanes ((final) m) :=by
  intro r
  let prior:=previousBank L argBase x (DescentOperandStateBanks.page f arg)
  let at_:=prior.base+(row H g₀ l.operandLanes r).val
  have lower: l.base≤ob:=(fences X l H g₀ k).1
  have middle : ob≤argBase :=by
    dsimp [Seed.Physical.bankStart,Seed.Columns.first,Seed.Columns.maskBase,Seed.stampStart]
    omega
  have low : header<at_:=by
    change header<argBase+_+_+_
    omega
  have before : at_<db :=by
    let nrows := H * chunks g₀ l.operandLanes
    let bankPage := (DescentOperandStateBanks.page f arg).val
    have row_lt : (row H g₀ l.operandLanes r).val < nrows := (row H g₀ l.operandLanes r).isLt
    have block_lt : x.val < 2^k := x.isLt
    have page_lt : bankPage < 7 * (3 * l.groupsPerNode) := (DescentOperandStateBanks.page f arg).isLt
    have within_block : x.val * nrows + (row H g₀ l.operandLanes r).val < 2^k * nrows := calc
      _ < x.val * nrows + nrows := Nat.add_lt_add_left row_lt _
      _ = (x.val + 1) * nrows := (Nat.succ_mul x.val nrows).symm
      _ ≤ 2^k * nrows := Nat.mul_le_mul_right nrows block_lt
    have within_pages : bankPage * (2^k * nrows) + (x.val * nrows + (row H g₀ l.operandLanes r).val) <
        (7 * (3 * l.groupsPerNode)) * (2^k * nrows) := calc
      _ < bankPage * (2^k * nrows) + (2^k * nrows) := Nat.add_lt_add_left within_block _
      _ = (bankPage + 1) * (2^k * nrows) := (Nat.succ_mul bankPage _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ page_lt
    change argBase + bankPage * (2^k * nrows) + x.val * nrows + (row H g₀ l.operandLanes r).val <
      argBase + (7 * (3 * l.groupsPerNode)) * (2^k * nrows) + _
    apply Nat.lt_of_lt_of_le _ (Nat.le_add_right ..)
    simpa only [Nat.add_assoc] using Nat.add_lt_add_left within_pages argBase
  have topBound : top≤finish:=(Nat.le_add_right top _).trans (Nat.le_add_right ..)
  have first:=(DescentDatedSeedStartup.Primitive.fences X S.copies l.seedWidth payload k H g₀ lanes finish)
  have limitBound : finish≤limit:=first.1.trans first.2
  have topSpace:=topBound.trans_lt (limitBound.trans_lt space)
  have old:=operand_read X (Equiv.refl _) digits hs l m fields topSpace f arg x r
  have beforeTop:=before.trans_le (fences X l H g₀ k).2.2
  let middleMem:=output X (Equiv.refl _) digits hs l m
  let cleared:=DescentPrivateHeader.initialized header middleMem
  let printed:=afterCountImage X digits publicWide l header m
  have node:=(chart).seedIssued top Q cleared (limitBound.trans_lt space)
  have primitive:=DescentDatedSeedStartup.Primitive.any X G op S.copies l.seedWidth Z payload k H g₀ lanes finish hs
    printed sourceSpace space machine live
  exact (primitive.2.2 at_ (.inl (beforeTop.trans_le topBound))).trans
    ((node.2.1 at_ (.inl beforeTop)).trans ((DescentPrivateHeader.initialized_frame header middleMem at_ (Nat.ne_of_gt low)).trans old))

theorem seed_operand_rows {w : ℕ} (m : Memory w) (fields : l.operandBits*l.operandLanes≤w)
    (early : header<l.base) (sourceSpace : publicWords X+DescentDyadicSpan.span jobs≤finish)
    (live : 0<lanes) (machine : payload≤w) (space : limit<2^w)
    (pg : Pages (ports).argumentsPerNode) (x : Fin (L).blocks) :
    ∃cells : Fin (L).hosts→Fin (L).groups→Cell ((ports).operandBits*(L).nodes),
      Reads (previousBank L (ports).archive.arguments x pg) cells (L).lanes ((final) m) :=by
  let key:=(finProdFinEquiv : (Fin 7×Fin (ports).argumentsPerNode)≃Fin (7*(ports).argumentsPerNode)).symm pg
  have eqn : page key.1 key.2=pg:=Equiv.apply_symm_apply _ _
  rw [←eqn]
  exact ⟨_,seed_operand_cells G op X digits publicWide l header payload Z m fields early sourceSpace live machine space
    key.1 key.2 x⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
