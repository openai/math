import OAI.Hierarchy.DescentPaidSweepRun
import OAI.Hierarchy.DescentReachedCountRepitch

namespace OAI
/-! # Reusing an earlier resolved target bank for the native funded and occupied books -/
namespace Hierarchy.DescentPaidResidentCount.Sweep.HeldRepacked
open DescentSIMDLookup DescentPackedZip DescentPackedActorMask DescentPackedColony DescentOrdinaryAtomFieldRAM
open DescentPacking.PackedMatch.Local ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable (base H G old M k paths cap b n p : ℕ) (field : Bank) (P : Ports paths) (operand : ℕ→Expr) (labels : Fin p→ Cell n)
local notation "C" => RoleCounts.Repitch.count H G old M k paths b base
local notation "phase_" => RoleCounts.Repitch.phase H G old M k paths b base
local notation "floor₀" => (C).roof
local notation "D₀" => paths*2^k
local notation "ids" => Expr.lookup field .row
local notation "px" => (C).expr
local notation "pb" => Sweep.paidBank floor₀ p D₀ cap b n H G M
local notation "ab" => Sweep.aliveBank floor₀ p D₀ cap b n H G M

def roof :=Sweep.roof floor₀ p D₀ cap b n H G M
def program (w : ℕ) := ((phase_ w P operand).program).seq
  (Sweep.program floor₀ D₀ cap b H G M labels ids px w)
def ticks (w : ℕ):=(phase_ w P operand).ticks+Sweep.ticks floor₀ D₀ cap b H G M labels ids px
def image {w : ℕ} (m : Memory w) :=
  Sweep.image floor₀ D₀ cap b H G M labels ids px ((phase_ w P operand).image m)


/-- The actual count repacking and both held-field sweeps execute on every memory. -/
theorem any {w : ℕ} (m : Memory w) (witness : Bank) (access : Accessible P witness H G M w base)
    (fence : field.Fits w base) (early : ∀x<2^k,(operand x).Fits w base)
    (bounds : roof base H G old M k paths cap b n p<2^w) :
    let out:=image base H G old M k paths cap b n p field P operand labels m
    (program base H G old M k paths cap b n p field P operand labels w).Exec m out
      (ticks base H G old M k paths cap b n p field P operand labels w) ∧
    CheapCode (program base H G old M k paths cap b n p field P operand labels w) ∧
    (∀q,q<base ∨ roof base H G old M k paths cap b n p≤q→ out q=m q) :=by
  intro out
  let front:=phase_ w P operand
  have chain:=RoleCounts.Repitch.intervals H G old M k paths b base
  have lo : base≤floor₀:=chain.1.trans chain.2
  have geom:=Sweep.geometry floor₀ p D₀ cap b n H G M
  have hi : floor₀≤roof base H G old M k paths cap b n p:=
    geom.1.trans (geom.2.1.trans ((Nat.le_add_right ..).trans
      (geom.2.2.1.trans (geom.2.2.2.1.trans (Nat.le_add_right ..)))))
  have first:=RoleCounts.Repitch.any H G old M k paths b base P witness operand m early access (hi.trans_lt bounds)
  have held : (ids).Fits w base:=⟨fence,trivial⟩
  have charged : (px).Fits w floor₀:=⟨(C).result_fits (hi.trans_lt bounds) le_rfl,trivial⟩
  have end_:=Sweep.any floor₀ D₀ cap b H G M labels ids px (front.image m)
    (ProtocolRAMGeneratedWrite.fits_mono _ lo held) charged bounds
  refine ⟨?_,?_,?_⟩
  · exact @Procedure.Exec.then w front.program (Sweep.program floor₀ D₀ cap b H G M labels ids px w)
      m (front.image m) out front.ticks (Sweep.ticks floor₀ D₀ cap b H G M labels ids px) first.1 end_.1
  · intro P₀ R₀ K₀ pc reg pub exit j
    exact @cheap_seq w front.program (Sweep.program floor₀ D₀ cap b H G M labels ids px w)
      (@front.cheap) (@end_.2.2) P₀ R₀ K₀ pc reg pub exit j
  · intro a h
    exact (end_.2.1 a (h.imp_left (fun q=>q.trans_le lo))).trans
      (first.2 a (h.imp_right (fun q=>hi.trans q)))

end
end Hierarchy.DescentPaidResidentCount.Sweep.HeldRepacked

end OAI
