import OAI.Hierarchy.DescentIncomingHosts
import OAI.Hierarchy.DescentCalendarNumbers

namespace OAI
/-! # Exact public host addresses for a dyadically rounded original schedule -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentCompiler.TerminalScale

theorem hostRows_at_date {S : AtomSchedule} {d k : ℕ} (base : S.initialSites=2^d) (radix : S.radix=2^k) (i : ℕ) :
    hostRows (S.hostSize i)=S.hostSize i :=by
  have physical : S.hostSize i=2^(d+(S.hostGain+k)*i):=by
    rw [AtomSchedule.hostSize,base,radix,←pow_add,←pow_mul,←pow_add]
  rw [physical]
  apply le_antisymm _ (hostPad _)
  exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) ((Nat.clog_le_iff_le_pow (by decide : 1<2)).2 le_rfl)

theorem incomingHosts_eq {S : AtomSchedule} {d k : ℕ} (base : S.initialSites=2^d) (radix : S.radix=2^k)
    (i : ℕ) (inside : i≤S.length) : incomingHosts S i=S.hostSize i :=
  le_antisymm ((hosts_bounds S i inside).2.trans_eq (hostRows_at_date base radix i)) (hosts_bounds S i inside).1

theorem all_incomingHosts_eq {S : AtomSchedule} {d k : ℕ} (base : S.initialSites=2^d)
    (radix : S.radix=2^k) (i : ℕ) : incomingHosts S i=S.hostSize (min i S.length) :=by
  by_cases yes : i≤S.length
  · rw [Nat.min_eq_left yes];exact incomingHosts_eq base radix i yes
  · have late : S.length≤ i:=by omega
    simp [incomingHosts,Nat.not_lt_of_ge late,Nat.min_eq_right late]

theorem rounded_host_rows {F : Type} [Field F] (G : PoweredGadget F) (t J f g reset M tail i : ℕ) :
    let S:=stageNumbers G t J f g reset (2^Nat.clog 2 M) tail
    hostRows (S.hostSize i)=S.hostSize i ∧ incomingHosts S i=S.hostSize (min i S.length) :=by
  intro S
  let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
  have b : S.initialSites=2^Nat.clog 2 M:=rfl
  have r : S.radix=2^k:=rfl
  exact ⟨hostRows_at_date b r i,all_incomingHosts_eq b r i⟩

end Hierarchy.DescentSixParty.NativePitch

end OAI
