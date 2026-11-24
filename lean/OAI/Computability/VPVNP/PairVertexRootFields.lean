import OAI.Computability.VPVNP.PairVertexGeometryRun
import OAI.Computability.VPVNP.PairVertexSiteSegments
import OAI.Computability.VPVNP.PairSimulationTerminalRootGatherImage
import OAI.Computability.VPVNP.PairTerminalGatherGeometry

/-!
# Entering the root gather from the actual bootstrap and geometry stages

The root row, vertex ordinal and directory heads come from the saved
bootstrap registers. The argument stride comes from the geometry word
at offset seven of the freshly published private frame.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation

open BurstRAM PrivateRAM LiveProgram
open scoped Fin.CommRing

namespace TerminalRootGather.Layout

variable {w : ℕ}

/-- Decode the terminal header and public operands into the gather layout for the specified
final site ordinal. -/
def ofHeader (degree : ℕ) (pub : Fin 11 → Word w) (hdr ordinal : Word w) (m : Memory w) : TerminalRootGather.Layout where
  vertex := ordinal.val
  sites := (m (hdr+7).val).val
  slots := (m (hdr+8).val).val
  widthHead := (m (hdr+9).val).val
  incomingHead := (m (hdr+10).val).val
  prefixHead := (m (hdr+11).val).val
  wires := (m (hdr+13).val).val
  n := (pub 6).val
  root := (m (hdr+6).val + m (hdr+15).val * ordinal).val
  stride := (NativeFrame.fromHeader degree pub hdr m).arguments.stride

theorem dest_eq (degree : ℕ) (pub : Fin 11 → Word w) (hdr ordinal : Word w) (m : Memory w) :
    (ofHeader degree pub hdr ordinal m).dest = (NativeFrame.fromHeader degree pub hdr m).arguments.base
      (ofHeader degree pub hdr ordinal m).root := rfl

end TerminalRootGather.Layout

namespace VertexRootFields

open VertexImage TerminalSiteStart TerminalRootGather LeafSourceLoad

variable {c : Constants} {degree a b p r w : ℕ} {leaf shrink refresh : VertexImage.Segment}
local notation "S" => segments (VertexGeometry.segment c degree a b) TerminalRootGather.segment leaf shrink refresh
variable {A : Placement (segments (VertexGeometry.segment c degree a b) TerminalRootGather.segment leaf shrink refresh) p r}
  {M : Machine w p r 11} {m : Memory w} {hdr ord : Word w} {boot geo : Config w p r}
  {vals : Static 34 → Word w}

local notation "L" => TerminalRootGather.Layout.ofHeader degree M.publicData hdr ord m

private theorem cast_val (x : Word w) : (x.val : Word w) = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)

theorem saved (hb : BootReady (M.publicData 6) hdr ord m (boot.reg ∘ bootBank A))
    (hg : VertexGeometry.Ready c degree a b A m M.publicData boot geo vals) :
    TerminalRootGather.Saved L (imageRegs A rfl) geo := by
  have keep (i : VertexImage.Saved) (hi : i ≠ histBase) :
      geo.reg (imageRegs A (rfl : S .rootFields = TerminalRootGather.segment) (save i)) = boot.reg (A.saved i) :=
    (imageRegs_saved A (rfl : S .rootFields = TerminalRootGather.segment) i) ▸ hg.saved i hi
  constructor
  · exact (keep ordinal (by decide)).trans (hb.ordinal.trans (cast_val _).symm)
  · exact (keep root (by decide)).trans (hb.root.trans (cast_val _).symm)
  · exact (keep finalSites (by decide)).trans (hb.sites.trans (cast_val _).symm)
  · exact (keep slots (by decide)).trans (hb.slots.trans (cast_val _).symm)
  · exact (keep widths (by decide)).trans (hb.widths.trans (cast_val _).symm)
  · exact (keep incoming (by decide)).trans (hb.incoming.trans (cast_val _).symm)
  · exact (keep prefixBase (by decide)).trans (hb.prefixPtr.trans (cast_val _).symm)
  · exact (keep wires (by decide)).trans (hb.wires.trans (cast_val _).symm)

theorem stride (hb : BootReady (M.publicData 6) hdr ord m (boot.reg ∘ bootBank A))
    (hg : VertexGeometry.Ready c degree a b A m M.publicData boot geo vals) :
    geo.privateMem (geo.privateMem ((L).n : Word w)+7) = ((L).stride : Word w) := by
  have hh : boot.reg (A.saved header) = hdr := hb.header
  have ptr := hg.geometry.pointer
  rw [hh] at ptr
  have cell := hg.fields (7 : Fin 12)
  rw [hh] at cell
  change geo.privateMem (geo.privateMem (((M.publicData 6).val : ℕ) : Word w)+7) = _
  rw [ptr,← Nat.cast_ofNat (R := Word w) (n := 7),← Nat.cast_add]
  exact cell

/-- Execute the gather at its installed image rows using the booted saved
bank and the stride installed by the geometry segment. -/
theorem gather (contains : Contains A M) (hb : BootReady (M.publicData 6) hdr ord m (boot.reg ∘ bootBank A))
    (hg : VertexGeometry.Ready c degree a b A m M.publicData boot geo vals) (fit : (L).Fits m) :
    ∃ out es, out.pc = A.dfsPC 0 ∧ out.persistent = geo.persistent ∧
      (∀ i, out.reg (A.dfs i) = geo.reg (A.dfs i)) ∧ (∀ i, out.reg (A.saved i) = geo.reg (A.saved i)) ∧
      Frame (imageRegs A (rfl : S .rootFields = TerminalRootGather.segment)) geo out ∧
      out.privateMem = TerminalRootGather.Layout.placed (L).dest ((L).packet m) geo.privateMem ∧
      Cost es (15+21*(L).degree+5*((L).packet m).length) (5*(L).degree+((L).packet m).length) ∧ Prefix M m geo es out :=
  image_run A rfl M contains L m fit geo hg.pc (saved hb hg) (cast_val _).symm (stride hb hg)

end VertexRootFields
end PairSimulation

end VPVNP
end Computability
end OAI
