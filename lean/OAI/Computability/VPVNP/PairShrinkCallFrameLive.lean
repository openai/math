import OAI.Computability.VPVNP.PairNativeFrameDescriptor
import OAI.Computability.VPVNP.PairNativeFrameRun
import OAI.Computability.VPVNP.PairShrinkCallABI
import OAI.Computability.VPVNP.PairShrinkRoleHandoff

/-!
# Shrink-map operands from the native private geometry

The terminal startup stores the pointer at the live length and the cache,
length and histogram at offsets 8, 9 and 11. The hidden handoff and the map
reload use these four cells, possibly at different points of the traversal.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCallFrameLive

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {w p r : ℕ}

/-- Private geometry read by the two native handoffs. -/
structure Stored (R : LeafArena.Regions) (n : ℕ) (mem : Word w → Word w) : Prop where
  pointer : mem (n : Word w) = (NativeFrame.frameBase R : Word w)
  cache : mem ((NativeFrame.frameBase R : Word w) + 8) = (R.cacheBase : Word w)
  length : mem ((NativeFrame.frameBase R : Word w) + 9) = (n : Word w)
  histogram : mem ((NativeFrame.frameBase R : Word w) + 11) = (R.histBase : Word w)

variable (degree : ℕ) (pub : Fin 11 → Word w) (m : Memory w)

/-- Both the startup `Result` and the geometry segment's `Ready` expose
this pointer and the twelve fields in its actual outgoing private memory. -/
theorem of_fields (header role : Word w) (priv : Word w → Word w)
    (pointer : priv (pub 6) = (NativeFrame.frameBase
      (NativeFrame.fromHeader degree pub header m) : Word w))
    (fields : ∀ j : Fin 12, priv ((NativeFrame.frameBase
      (NativeFrame.fromHeader degree pub header m) + j.val : ℕ) : Word w) =
      NativeFrame.fields degree pub header role m j) :
    Stored (NativeFrame.fromHeader degree pub header m) (pub 6).val priv := by
  have atField (j : Fin 12) : priv ((NativeFrame.frameBase
      (NativeFrame.fromHeader degree pub header m) : Word w) + (j.val : Word w)) =
      NativeFrame.fields degree pub header role m j := by
    rw [← Nat.cast_add]
    exact fields j
  refine ⟨?_, atField 8, ?_, atField 11⟩
  · rw [Fin.cast_val_eq_self]; exact pointer
  · exact (atField 9).trans (Fin.cast_val_eq_self _).symm

/-- Concrete initial private geometry of a completed frame program. -/
theorem of_run (P : NativeFrame.Ports r) (c out : Config w p r)
    (run : NativeFrame.Result P degree pub m c out) :
    Stored (NativeFrame.fromHeader degree pub (c.reg P.header) m) (pub 6).val out.privateMem :=
  of_fields degree pub m (c.reg P.header) (c.reg P.role) out.privateMem run.pointer run.values

/-- Rewrite the runtime region to the selected terminal row layout. -/
theorem of_readback {first rows stride baseRadix laneRadix n labels : ℕ} {header span : Word w}
    {priv : Word w → Word w}
    (read : NativeFrame.Readback m header first rows stride baseRadix laneRadix span)
    (source : Stored (NativeFrame.fromHeader degree pub header m) (pub 6).val priv)
    (length : (pub 6).val = n) (labelCount : (pub 9).val = labels)
    (room : first + rows < 2 ^ w) :
    Stored (TerminalLayout.privateRegions degree n (first + rows) labels) n priv := by
  rw [read.regions_eq degree pub n labels length labelCount room, length] at source
  exact source

variable {R : LeafArena.Regions} {n : ℕ} {before after : Word w → Word w}

/-- Only the geometry pointer and its three live fields need to survive the
private packet writes between startup and the handoffs. -/
theorem Stored.transfer (h : Stored R n before)
    (ptr : after (n : Word w) = before (n : Word w))
    (cells : ∀ j ∈ ([8, 9, 11] : List ℕ), after ((NativeFrame.frameBase R + j : ℕ) : Word w) =
      before ((NativeFrame.frameBase R + j : ℕ) : Word w)) : Stored R n after := by
  have field (j : ℕ) (mem : j ∈ ([8, 9, 11] : List ℕ)) :
      after ((NativeFrame.frameBase R : Word w) + (j : Word w)) =
      before ((NativeFrame.frameBase R : Word w) + (j : Word w)) := by
    rw [← Nat.cast_add]
    exact cells j mem
  exact ⟨ptr.trans h.pointer, (field 8 (by decide)).trans h.cache,
    (field 9 (by decide)).trans h.length, (field 11 (by decide)).trans h.histogram⟩

/-- Reading the geometry in the hidden handoff and then in the map reload
sets the two concrete registers required by the party publication theorem. -/
theorem handoff (hiddenFrame : Stored R n before) (mapFrame : Stored R n after)
    (cfg : Config w p r) (common : Fin 24 ↪ Fin r)
    (hidden : cfg.reg (common 8) = VertexLevel.hiddenBaseWord
      (before (before (n : Word w) + 8)) (before (before (n : Word w) + 9)))
    (hist : cfg.reg (common 10) = after (after (n : Word w) + 11)) :
    cfg.reg (common 8) = (ShrinkCallABI.hiddenBase R n : Word w) ∧
      cfg.reg (common 10) = (R.histBase : Word w) := by
  rw [hiddenFrame.pointer, hiddenFrame.cache, hiddenFrame.length, VertexLevel.hiddenBaseWord_cast]
    at hidden
  rw [mapFrame.pointer, mapFrame.histogram] at hist
  exact ⟨hidden, hist⟩

end PairSimulation.ShrinkCallFrameLive

end VPVNP
end Computability
end OAI
