import OAI.Hierarchy.DescentDatedTerminalAperture
import OAI.Hierarchy.DescentTerminalFundedPreflight
import OAI.Hierarchy.DescentTerminalPacketHomeInstall
import OAI.Hierarchy.DescentTerminalBookBitPrice

namespace OAI
/-! # Last address of packet home installation and the three purchased scan tables -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open DescentDatedAddressBook DescentTerminalPreflightSpace DescentTerminalPacketHomeRAM
open DescentTerminalPrimitiveArena DescentTerminalLocalPortBook Filter
noncomputable section

def sourcesBase (x:Spec) (base rows q:ℕ) := (x.scanPages (Expansion.stop base rows) q).stop

theorem sources_base_eq (x:Spec) (base rows q:ℕ) :
    sourcesBase x base rows q=base+pad rows+pad rows+(pad x.controlBytes+pad x.paidRows+(x.paidRows+1)) := rfl

private theorem purchased_sources (x:ℕ→Spec) (base rows q:ℕ→ℕ)
    (earlier:TerminalBound base) (packing:TerminalBound rows)
    (books:TerminalBound (fun h=>(x h).controlBytes)) (paid:TerminalBound (fun h=>(x h).paidRows)) :
    TerminalBound (fun h=>sourcesBase (x h) (base h) (rows h) (q h)) := by
  have invoice:=((earlier.add packing.padded).add packing.padded).add
    ((books.padded.add paid.padded).add (paid.add (Bounded.const 1)))
  simpa only [sources_base_eq,pad] using invoice

/-- Both public packet views cost a padded row each. The count, remainder and boundary arrays
obtain their limits from the calibrated finite control alphabet and paid site rows. -/
theorem sources_rate (x:ℕ→Spec) (base rows q scale paid:ℕ→ℕ)
    (earlier:TerminalBound base) (packing:TerminalBound rows) (billed:TerminalBound paid)
    (preflight:∀ᶠ h:ℕ in atTop,(x h).ScalarRoom h (scale h) (paid h)) :
    TerminalBound (fun h=>sourcesBase (x h) (base h) (rows h) (q h)) := by
  have books:TerminalBound (fun h=>(x h).controlBytes):=by
    refine ⟨1,?_⟩
    filter_upwards [preflight] with h ready
    intro _
    exact ready.book.trans (Nat.pow_le_pow_right (by decide) (by simpa only [Nat.one_mul] using Nat.div_le_self h 2))
  obtain ⟨K,budget⟩:=billed
  have paidRows:TerminalBound (fun h=>(x h).paidRows):=by
    refine ⟨K,?_⟩
    filter_upwards [preflight,budget] with h ready bound
    intro _
    exact (Nat.le_add_right ..).trans (ready.rows.trans (bound ()))
  exact purchased_sources x base rows q earlier packing books paidRows

/-- A direct bound from the three finite geometry dimensions, without a preflight certificate.
The compact mixed-radix byte array is the genuine code of four gate bits, local names and arguments. -/
theorem sources_rate_geometry (x:ℕ→Spec) (base rows q g:ℕ→ℕ) (K:ℕ)
    (earlier:TerminalBound base) (packing:TerminalBound rows) (paid:TerminalBound (fun h=>(x h).paidRows))
    (coordinates:∀ᶠ h:ℕ in atTop,0<g h ∧ (x h).vertices≤g h ∧
      (x h).vertices*(x h).arguments≤g h ∧ (x h).arguments≤g h ∧ g h*g h≤K*h) :
    TerminalBound (fun h=>sourcesBase (x h) (base h) (rows h) (q h)) := by
  have books:TerminalBound (fun h=>(x h).controlBytes):=by
    refine ⟨60*K,?_⟩
    filter_upwards [coordinates] with h bounds
    intro _
    obtain ⟨pos,v,m,a,quad⟩:=bounds
    have size:=Book.bytes_envelope (x h).vertices (x h).arguments (g h) v m a pos
    exact size.trans (Nat.pow_le_pow_right (by decide) (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 60 quad))
  exact purchased_sources x base rows q earlier packing books paid

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
