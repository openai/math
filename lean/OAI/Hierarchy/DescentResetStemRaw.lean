import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Scalar stem descriptors in row-major storage before broadcast -/
namespace Hierarchy.DescentResetStemHeaders
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

def Raw {w K H b : ℕ} (raw : ℕ) (β : Fin K → Fin H → Cell b) (m : Memory w) : Prop :=
  ∀ j v, m (raw+j.val*H+v.val)=((β j v).val : Word w)

end Hierarchy.DescentResetStemHeaders

end OAI
