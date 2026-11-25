import OAI.Hierarchy.DescentSeedChosenLayoutCore
import OAI.Hierarchy.DescentSeedNativeGeometryPrice
import OAI.Hierarchy.DescentSeedResetFill
import OAI.Hierarchy.DescentSeedFirstDonorRate
import OAI.Hierarchy.DescentSeedStageCharge

namespace OAI
/-! # Choosing the two initialization pitches from the actual first two readers -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentSixParty DescentPackedWalsh DescentSIMDLookup DescentSeedRoot
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)
theorem selected_venue_fill (h words factor gain k tail p f quota : ℕ)
    (groups : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (cpu : words ≤ factor*h) (pos : 0 < firstDonor G S gain k p)
    (donor : 2*firstDonor G S gain k p ≤ h) (walsh : 0 < firstPrecision S k tail p f quota)
    (can : k ≤ laneBits (S.groupWidth k tail 0+k) h (firstPrecision S k tail p f quota)) :
    S.groupCount 0 ≤ venuePitch G S h gain k tail p f quota ∨
      words ≤ venuePitch G S h gain k tail p f quota*venuePrice G S factor gain k tail p f quota :=by
  by_cases ordinary : S.rounds=0
  · simpa only [venuePitch,venuePrice,ite_eq_left ordinary] using
      reset_fill S k tail 0 h words factor (firstPrecision S k tail p f quota) groups radix walsh can cpu
  · right
    simpa only [venuePitch,venuePrice,ite_eq_right ordinary] using
      pitch_fill h (firstDonor G S gain k p) words factor pos donor cpu

theorem selected_operand_fill (h words factor k tail p drift degree : ℕ)
    (cpu : words ≤ factor*h) (room : 4*DescentOperandWidth.recordBits G S k tail drift degree p ≤ h) :
    let r:=DescentOperandWidth.recordBits G S k tail drift degree p
    words ≤ lanes h (2*r)*(8*factor*r) :=by
  intro r
  have live : 0 < r :=by dsimp only [r,DescentOperandWidth.recordBits];omega
  have got:=pitch_fill h (2*r) words factor (by omega) (by omega) cpu
  simpa only [show 4*factor*(2*r)=8*factor*r by ring] using got

end Hierarchy.DescentDatedSeedStartup

/-! # The actual first CPU bill occupies the zero date of the selected schedule -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentCompiler DescentSixParty DescentPackedWalsh DescentSIMDLookup DescentInitialHost DescentSeedRoot
open DescentColonies DescentDyadicSpan DescentPackedSeed Catalyst
noncomputable section
private theorem chunk_pos {g m : ℕ} (n : 0 < g) (p : 0 < m) : 0 < chunks g m :=by
  change 0 < (g+m-1)/m
  exact Nat.div_pos (by omega) p

variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)
  (h w factor k tail gain p drift degree f quota base field wire history header : ℕ)
local notation "l" => selectedLayout G S h k tail gain p drift degree f quota base field wire history
local notation "r" => 2^k
local notation "orec" => DescentOperandWidth.recordBits G S k tail drift degree p
local notation "orig" => S.firstWidth G.b p
local notation "W" => venuePrice G S factor gain k tail p f quota
local notation "price" => highPrice factor (orig/p) r
local notation "low" => lowPrice (orig/p) W (8*factor*orec) (4*factor*digitsNeeded orig)
variable {cp pins : ℕ} (X : Approximation F cp pins) (digits : Fin S.copies≃Fin (S.groupCount 0)×Block k)
    (publicWide : Fintype.card (Vertex X) ≤ DescentDyadicSpan.span (AtomSchedule.initialSites S))
local notation "ticks" => wideTicks (S:=S) (k:=k) (H:=DescentDyadicSpan.span (AtomSchedule.initialSites S)) X l h+7*DescentStaticWordColumn.names (wideNode X digits publicWide l header h w)

theorem selected_cpu (host : 0 < S.initialSites) (groups : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (cpu : w+1 ≤ factor*h) (positive : 0 < firstDonor G S gain k p) (space : 2*firstDonor G S gain k p ≤ h)
    (walsh : 0 < firstPrecision S k tail p f quota)
    (can : k ≤ laneBits (S.groupWidth k tail 0+k) h (firstPrecision S k tail p f quota))
    (opRoom : 4*orec ≤ h) (selRoom : 2*digitsNeeded orig ≤ h) :
    (ticks)*(w+1) ≤ S.hostSize 0*h*price+S.hostSize 0*(S.groupCount 0*S.radix)*low :=by
  have enough:=selected_venue_fill G S h (w+1) factor gain k tail p f quota groups radix cpu positive space walsh can
  have used:=selected_operand_fill G S h (w+1) factor k tail p drift degree cpu opRoom
  have marked:=selector_fill l h factor (w+1) selRoom cpu
  have occ : 0 < S.groupCount 0 :=by
    rw [AtomSchedule.groupCount,groups,radix]
    positivity
  have m : 0 < (l).packedLanes :=by
    change 0 < venuePitch G S h gain k tail p f quota
    unfold venuePitch
    split
    · exact Nat.two_pow_pos _
    · exact (occupancy h _ positive space).1
  have o : 0 < (l).operandLanes :=by
    change 0 < lanes h (2*orec)
    have rr : 0 < orec := (Nat.succ_pos (Nat.log 2 p)).trans_le (Nat.le_max_right _ _)
    have rrPair : 0 < 2*orec := Nat.mul_pos (by decide : 0 < 2) rr
    have fits : 2*(2*orec) ≤ h := by simpa only [← Nat.mul_assoc] using opRoom
    exact (occupancy h (2*orec) rrPair fits).1
  have bill:=wide_rectangle X digits publicWide l header h w (span_pos S.initialSites) (chunk_pos occ m) (chunk_pos occ o)
    W (8*factor*orec) (4*factor*digitsNeeded orig) enough used marked
  exact rectangle_at_zero S h (w+1) factor (span S.initialSites) (S.groupCount 0) r (orig/p) W (8*factor*orec) (4*factor*digitsNeeded orig)
    ((ticks)*(w+1)) host le_rfl cpu rfl radix.symm bill

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
