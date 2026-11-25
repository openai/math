import OAI.Hierarchy.DescentResetPeerJointPacked
import OAI.Hierarchy.DescentResetPeerJointBroadcast
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Four original compact peer coordinates and their shared packed broadcast -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSIMDLookup Filter
noncomputable section
namespace JointAtlas
def rowsEnd (base H sparse : ℕ) :=DescentResetPeerJointRAM.endAddress base H sparse
def endAddress (base H sparse G M bits : ℕ) :=
  DescentResetPeerJointPacked.completeEnd base H sparse G M bits
theorem shift (base H sparse G M bits : ℕ) :
    endAddress base H sparse G M bits=base+endAddress 0 H sparse G M bits :=
  DescentResetPeerJointPacked.complete_shift base H sparse G M bits


variable {ι : ℕ→Type*} {H sparse G M bits : ∀h,ι h→ℕ}
theorem rate (hosts : Bounded H) (raw : Bounded sparse) (groups : Bounded G) (batch : Bounded M)
    (alphabet : Bounded (fun h i=>2^(bits h i))) :
    Bounded (fun h i=>endAddress 0 (H h i) (sparse h i) (G h i) (M h i) (bits h i)) :=by
  let c (n:ℕ):=Bounded.const (ι:=ι) n
  have gather:=((((c 0).add ((c 3).mul raw.padded)).add ((c 4).mul hosts)).add hosts.padded)
  have parts : Bounded (fun h i=>chunks (G h i) (M h i)) :=
    (groups.add batch).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have pairs:=(c 2).mul (hosts.mul parts)
  have lut:=pairs.add ((batch.add (c 1)).mul alphabet)
  exact (((gather.add pairs).add (lut.add (c 1)).padded).add ((c 4).mul hosts)).add hosts.padded
end JointAtlas
end
end Hierarchy.DescentDatedAddressBook

end OAI
