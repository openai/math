import OAI.Hierarchy.DescentTerminalPaidBoot
import OAI.Hierarchy.DescentTerminalAddressPlan
import OAI.Hierarchy.DescentTerminalEmitterFront

namespace OAI
/-! # The terminal exterior flight and public scan preserve the original paid raw rows -/
namespace Hierarchy.DescentTerminalPaidBoot
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open DescentExteriorShelf
open scoped Fin.CommRing
noncomputable section
variable {w K W q piece : ℕ}
local notation "B" => q*(W*piece)

theorem exteriorRows_low (s : DescentTerminalDataPlane.Shape) (l : DescentTerminalDataPlane.Layout)
    (m : Memory w) {x : ℕ} (outside : x < l.exterior) (pub : x < l.output.base) :
    DescentTerminalDataPlane.exteriorRows s l m x = m x := by
  have sticky : x < flagOut (j:=s.headBits) (r:=s.restBits) (t:=s.bitLanes) (e:=s.exteriors) l.exterior :=
    outside.trans_le (Nat.le_add_right ..)
  have first : x < start s.headBits s.restBits s.bitLanes s.exteriors l.exterior :=
    outside.trans_le (Nat.le_add_right ..)
  have key : x < keyAt s.headBits s.restBits s.bitLanes s.exteriors l.exterior :=
    outside.trans_le (Nat.le_add_right ..)
  rw [DescentTerminalDataPlane.exteriorRows,DescentTerminalChipRuntime.image_low _ _ _ _ pub,
    DescentTerminalDataPlane.exterior,flaggedMem,DescentExteriorRejectWord.before _ _ _ sticky]
  unfold serviceMemory DescentExteriorFetch.finalMem
  rw [DescentTerminalChipRuntime.image_low _ _ _ _ (by omega),
    DescentTerminalChipRuntime.image_low _ _ _ _ (by omega),
    DescentTerminalChipRuntime.image_low _ _ _ _ first,
    DescentTerminalChipRuntime.image_low _ _ _ _ key]

/-- The actual candidate bank supplies the hidden sector of the raw join after
both native flights and the dense public row publication, for every paid choice. -/
theorem hidden (s : DescentTerminalDataPlane.Shape) (l : DescentTerminalDataPlane.Layout)
    (z : Input K W q piece s.rawRows → Bool) (w codes origin : ℕ) (m : Memory w)
    (alias_ : l.candidate = candidate K W q piece codes s.rawRows origin)
    (before : l.candidate.base+l.candidate.size ≤ l.exterior)
    (publicAfter : l.exterior ≤ l.output.base)
    (kept : ∀ j < total K W q piece codes s.rawRows, m (origin+j) = back z w codes j)
    (i : Fin s.rawRows) :
    DescentTerminalDataPlane.exteriorRows s l m (l.candidate.base+i.val) =
      ((dense B (stream (z ∘ Sum.inr)) i.val).val : Word w) := by
  have cap : s.rawRows ≤ l.candidate.size := by
    rw [alias_]
    exact candidate_size K W q piece codes s.rawRows origin
  have low := (Nat.add_lt_add_left (i.isLt.trans_le cap) l.candidate.base).trans_le before
  rw [exteriorRows_low s l m low (low.trans_le publicAfter),alias_]
  exact rawRead z w codes origin m kept i

end
end Hierarchy.DescentTerminalPaidBoot

namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open scoped Fin.CommRing
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalRowArena DescentTerminalVertexFields
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow
noncomputable section
variable {blocks K W q piece w : ℕ}
local notation "B" => q*(W*piece)

/-- On the true allocated data plane the bank ends below takeoff by the input's original address. -/
theorem paid_hidden (S : Shape) (I : Input) (base : ℕ) (F : MaskedShelf blocks)
    (old : Earlier S I base F w) (z : DescentTerminalPaidBoot.Input K W q piece S.terminal.plane.rawRows → Bool)
    (codes origin : ℕ) (m : Memory w)
    (alias_ : I.candidate = DescentTerminalPaidBoot.candidate K W q piece codes S.terminal.plane.rawRows origin)
    (kept : ∀ j < DescentTerminalPaidBoot.total K W q piece codes S.terminal.plane.rawRows,
      m (origin+j) = DescentTerminalPaidBoot.back z w codes j) (i : Fin S.terminal.plane.rawRows) :
    DescentTerminalDataPlane.exteriorRows S.terminal.plane (bodyPlane S I base) m
      (I.candidate.base+i.val) = ((dense B (stream (z ∘ Sum.inr)) i.val).val : Word w) :=
  DescentTerminalPaidBoot.hidden S.terminal.plane (bodyPlane S I base) z w codes origin m
    alias_ old.assignment (Nat.le_add_right ..) kept i

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
