import OAI.Hierarchy.DescentSeedHeaderLayout

namespace OAI
/-! # The seed header precedes the register directories and token transposition -/
namespace Hierarchy.DescentDatedSeedStartup.SeedHeader.Input
open DescentSixParty DescentSeedRoot DescentPackedSeed DescentOperandStateBanks DescentInitialHost Catalyst
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (v : SeedHeader.Input F) (G : PoweredGadget F) (op : RotorSpec)
  (t f g drift h : ℕ)
local notation "s" => v.width G
local notation "R" => v.schedule.copies
local notation "groups" => v.schedule.groupCount 0
local notation "l" => v.layout G t f g drift h
local notation "top" => endAddress v.circuit l v.hosts groups v.k
local notation "finish" => (DescentDatedSeedStartup.Input.nodeChart l v.k v.hosts groups).seedEnd top
local notation "M" => Primitive.paletteLanes G op s (v.schedule.grainAt G.b v.p 0) h v.k

theorem base_le_floor : v.base G h ≤ v.floor G op t f g drift h := by
  have signed : (l).base ≤ operandBase v.circuit l v.hosts groups :=by
    unfold operandBase Signed.Plane.endAddress Signed.Plane.output
    omega
  have operands : operandBase v.circuit l v.hosts groups ≤ directoryBase v.circuit l v.hosts groups v.k :=by
    unfold directoryBase Seed.Physical.endAddress Seed.Physical.bankStart Seed.Columns.first
      Seed.Columns.maskBase Seed.stampStart
    simp only [Nat.add_assoc]
    exact Nat.le_add_right ..
  have directory : directoryBase v.circuit l v.hosts groups v.k ≤ top := Nat.le_add_right ..
  have nodes : top ≤ finish := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  let splitAt := DescentPackedSeed.Primitive.Source.finish v.circuit R s h finish
  have source : finish ≤ splitAt :=by
    dsimp only [splitAt,DescentPackedSeed.Primitive.Source.finish,DescentPackedSeed.Primitive.Source.raw]
    omega
  let count := Fintype.card (Old v.circuit)
  let a := DescentPackedSeed.Primitive.roleBits s
  let lanes := DescentPackedSeed.Primitive.pieces h s
  have narrow := DescentSeedTokenTransposition.Narrow.cut_eq splitAt count groups (2^v.k) a lanes M
  have last : splitAt ≤ Primitive.initialEnd v.circuit R s h v.k v.hosts groups M finish :=by
    change splitAt ≤ DescentSeedTokenTransposition.endAddress splitAt count v.hosts groups (2^v.k) a lanes M
    simp only [DescentSeedTokenTransposition.endAddress,DescentSeedTokenTransposition.out,
      DescentSeedTokenColumns.out,DescentSeedTokenTransposition.cut,narrow,Nat.add_assoc]
    exact Nat.le_add_right ..
  exact signed.trans (operands.trans (directory.trans (nodes.trans (source.trans last))))

end
end Hierarchy.DescentDatedSeedStartup.SeedHeader.Input

end OAI
