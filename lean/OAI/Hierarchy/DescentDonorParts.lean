import OAI.Hierarchy.DescentDonorWidths
import OAI.Hierarchy.DescentPackedDonorEncoding

namespace OAI
/-! # The packed fields of a donor window -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM
open DescentSIMDLookup
noncomputable section
variable (s : Shape)

structure Parts where
  terrain : Cell (rawBits s)
  cables : Cell (cableBits s)
  owners : Cell (ownerBits s)
  chart : Cell (chartBits s)
  hub : Cell (chartBits s)
  births : Cell (freshBits s)

def combine (x : Parts s) : Cell (totalBits s) :=
  pair _ _ (pair _ _ (pair _ _ (x.terrain,x.cables),pair _ _ (x.owners,x.chart)),pair _ _ (x.hub,x.births))

def separate (v : Cell (totalBits s)) : Parts s :=
  let mid:=(pair ((rawBits s+cableBits s)+(ownerBits s+chartBits s)) (chartBits s+freshBits s)).symm v
  let one:=(pair (rawBits s+cableBits s) (ownerBits s+chartBits s)).symm mid.1
  let b:=(pair (chartBits s) (freshBits s)).symm mid.2
  let a:=(pair (rawBits s) (cableBits s)).symm one.1
  let c:=(pair (ownerBits s) (chartBits s)).symm one.2
  ⟨a.1,a.2,c.1,c.2,b.1,b.2⟩

@[simp] theorem separate_combine (v : Parts s) : separate s (combine s v)=v := by
  cases v;simp [separate,combine]

end
end Hierarchy.DescentRawCablePanel.DepotRAM

end OAI
