import OAI.Hierarchy.DescentDatedSeedExtent
import OAI.Hierarchy.DescentDatedSeedNodes
import OAI.Hierarchy.DescentDatedSeedStartup
import OAI.Hierarchy.DescentOperandSeedPhysical
import OAI.Hierarchy.DescentDatedPublicFloor

namespace OAI
/-! # The first public age starts after the issued seed, its argument book and the actual roster -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentOperandStateBanks DescentPackedSeed DescentSeedRoot DescentInitialHost DescentSIMDLookup
open DescentDatedAddressBook Filter Catalyst
open scoped Classical
noncomputable section

theorem initial_floor {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)
    (l : Layout) (H G d : ℕ) :
    (Input.nodeChart l d H G).seedEnd (endAddress X l H G d)=
      seededFloor l.base (Fintype.card (Vertex X)) H G l.packedLanes l.operandLanes d l.groupsPerNode :=rfl

theorem seeded_rate {ι : ℕ→Type*} {base v H G M T d N : ∀h,ι h→ℕ}
    (first : Bounded base) (vertices : Bounded v) (hosts : Bounded H) (groups : Bounded G)
    (lanes : Bounded M) (operandLanes : Bounded T) (blocks : Bounded (fun h i=>2^(d h i))) (arguments : Bounded N) :
    Bounded (fun h i=>seededFloor (base h i) (v h i) (H h i) (G h i) (M h i) (T h i) (d h i) (N h i)) := by
  have batch : Bounded (fun h i=>chunks (G h i) (M h i)) :=
    (groups.add lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have rows:=hosts.mul batch
  have operandBatch : Bounded (fun h i=>chunks (G h i) (T h i)) :=
    (groups.add operandLanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have operandRows:=hosts.mul operandBatch
  have args:=blocks.mul operandBatch
  have plane:=((Bounded.const (2*256)).mul hosts).mul batch
  have stage:=first.add ((((vertices.mul (Bounded.const (2*3))).add (Bounded.const 1)).padded).add
    ((Bounded.const 2).mul plane.padded))
  have tags:=vertices.mul (Bounded.const 3)
  have wave:=(((stage.add plane).add (vertices.mul (Bounded.const (3*2)))).add tags).add args.padded
  have width:=(Bounded.const 7).mul ((Bounded.const 3).mul arguments)
  have write:=((wave.add args.padded).add (width.mul (blocks.mul operandRows))).add ((operandRows.add (Bounded.const 1)).padded)
  have issued:=write.add ((Bounded.const (3+8)).mul (hosts.max' ((hosts.mul (Bounded.const 3)).max' rows)).padded)
  exact (issued.add (((Bounded.const 2).mul blocks).mul operandRows)).add (operandRows.add (Bounded.const 1)).padded

end
end Hierarchy.DescentDatedSeedStartup

end OAI
