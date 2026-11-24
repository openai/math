import OAI.Computability.VPVNP.PairVertexRootFields

/-! # Physical inputs of the terminal root at one ordinal -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalProgram

open BurstRAM PrivateRAM Compression
open scoped Fin.CommRing

/-- Native gather and bootstrap inputs at a physical ordinal. -/
structure RootInputs {w a g : ℕ} (Y : State a g) (v : Y.network.Site) (degree : ℕ)
    (pub : Fin 11 → Word w) (hdr state : Word w) (m : Memory w)
    (bits : Fin (∑ j, TerminalPrefix.width Y j) → Bool) : Prop where
  active : state < m (hdr+7).val
  rootPos : 0 < (TerminalRootGather.Layout.ofHeader degree pub hdr state m).root
  rootBound : (TerminalRootGather.Layout.ofHeader degree pub hdr state m).root <
    (NativeFrame.fromHeader degree pub hdr m).nodes
  cache : (NativeFrame.fromHeader degree pub hdr m).cacheBase+38 ≤ 2^w
  numbering : TerminalGatherGeometry.Numbering Y (TerminalRootGather.Layout.ofHeader degree pub hdr state m) v
  rows : TerminalGatherGeometry.Rows Y (TerminalRootGather.Layout.ofHeader degree pub hdr state m) m
  bank : ∀ i, m ((TerminalRootGather.Layout.ofHeader degree pub hdr state m).wires+i.val) = PrivateFields.bitValue w (bits i)
  fits : (TerminalRootGather.Layout.ofHeader degree pub hdr state m).Fits m
  deg : 2^a ≤ degree
  width : Y.maxWireWidth ≤ (pub 6).val
  header : hdr.val + 31 < 2^w
  heads : ∀ h ∈ [(TerminalRootGather.Layout.ofHeader degree pub hdr state m).incomingHead,
    (TerminalRootGather.Layout.ofHeader degree pub hdr state m).widthHead,
    (TerminalRootGather.Layout.ofHeader degree pub hdr state m).prefixHead], h+TerminalPrefix.arcCount Y ≤ hdr.val
  wires : (TerminalRootGather.Layout.ofHeader degree pub hdr state m).wires + Y.totalWidth ≤ hdr.val

end PairSimulation.TerminalProgram

end VPVNP
end Computability
end OAI
