import OAI.Hierarchy.DescentResetRetainedCalendarWidths
import OAI.Hierarchy.DescentDateBillRowRatio
import OAI.Hierarchy.DescentWalshDyadicChosen

namespace OAI
/-! # Actual local ROM and host scan geometry for the retained chronological canvas -/
namespace Hierarchy.DescentSixParty.AtomSchedule
open DescentCompiler DescentPackedWalsh DescentSIMDLookup DescentPacking.PackedMatch.Local
noncomputable section
variable {F : Type} [Field F] (S : DescentCompiler.AtomSchedule) (G : PoweredGadget F)

theorem retainedApertures (k tail drift degree p age h oldNodes oldArgs oldLanes : ℕ)
    (base : S.baseGroups=2^tail) (radix : S.radix=2^k) (ageBound : age<S.length)
    (ns : oldNodes≤S.retainedNodes) (args : oldArgs≤S.retainedArgumentsAt G drift)
    (short : 8*(S.retainedWidth G k tail drift degree p)≤h) :
    let L:=S.retainedFromPrevious G k tail drift degree p age h oldNodes oldArgs oldLanes
    L.wholeWord*L.gatherLanes≤h/2 ∧ (L.bits*L.blocks+L.bits)*L.gatherLanes≤h/2 ∧
    (L.siteWord+L.stripWord)*L.decodedLanes≤h/2 ∧ L.siteWord*L.decodedLanes≤h/2 :=by
  intro L
  let z:=S.retainedWidth G k tail drift degree p
  let c:=S.groupWidth k tail age
  let e:=S.retainedExponent G k tail drift degree p age h
  have nonzero : 0<z:=(by exact Nat.le_max_left 1 _)
  have keys:=keys_fit (m:=c) nonzero short
  change 1+(z+z)*2^e≤h/2 at keys
  have aperture : z*2^e≤h/2:=by rw [Nat.add_mul] at keys;omega
  have mag:=S.previousWidth G k tail drift degree p age h oldNodes oldArgs oldLanes ns args base radix ageBound
  have j : L.bits*L.blocks+L.bits≤z:=(Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
  have used {v : ℕ} (vle : v≤z) : v*2^e≤h/2 :=(Nat.mul_le_mul_right (2^e) vle).trans aperture
  exact ⟨used mag.1,used j,used mag.2,used ((Nat.le_add_right ..).trans mag.2)⟩

/-- The selector LUT reads one original remixed stripe and the true per-primary sorted roster. -/
theorem retainedSelectorAperture (k tail drift degree p age h oldNodes oldArgs oldLanes : ℕ)
    (base : S.baseGroups=2^tail) (radix : S.radix=2^k) (ageBound : age<S.length)
    (short : 8*(S.retainedWidth G k tail drift degree p)≤h) :
    let L:=S.retainedFromPrevious G k tail drift degree p age h oldNodes oldArgs oldLanes
    (L.stripWord+L.donors*Nat.clog 2 (L.donors+1))*L.decodedLanes≤h/2:=by
  intro L
  let z:=S.retainedWidth G k tail drift degree p
  let e:=S.retainedExponent G k tail drift degree p age h
  have positive : 0<z:=Nat.le_max_left 1 _
  have keys:=keys_fit (m:=S.groupWidth k tail age) positive short
  change 1+(z+z)*2^e≤h/2 at keys
  rw [Nat.add_mul] at keys
  have lim:=S.selector_width G k tail drift degree p age h oldNodes oldArgs oldLanes base radix ageBound
  have aperture : z*2^e≤h/2 :=
    (Nat.le_add_right (z*2^e) (z*2^e)).trans ((Nat.le_add_left _ 1).trans keys)
  exact (Nat.mul_le_mul_right (2^e) lim).trans aperture

theorem retainedRows (k tail drift degree p age h u oldNodes oldArgs oldLanes : ℕ)
    (_base : S.baseGroups=2^tail) (_radix : S.radix=2^k) (_ageBound : age<S.length)
    (pitch : 0<lanes h u) :
    let L:=S.retainedFromPrevious G k tail drift degree p age h oldNodes oldArgs oldLanes
    L.rows≤(16*(S.retainedWidth G k tail drift degree p))*Stage.DateBill.words L.hosts L.grouped h u :=by
  intro L
  let b:=S.retainedWidth G k tail drift degree p
  let c:=S.groupWidth k tail age
  let M:=2^(laneBits c h b)
  have positive : 0<b:=Nat.le_max_left 1 _
  apply Stage.DateBill.pitched_rows L.hosts (2^c) h u M (16*b) (Nat.two_pow_pos _) pitch
  rcases DescentWalshDyadicBudget.laneBits_median c h b positive with all | funded
  · left
    change 2^c≤16*b*2^(laneBits c h b)
    rw [all]
    have one : 1≤16*b:=by omega
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2^c) one
  · right
    exact (Nat.div_le_self h (2*u)).trans funded

end
end Hierarchy.DescentSixParty.AtomSchedule

end OAI
