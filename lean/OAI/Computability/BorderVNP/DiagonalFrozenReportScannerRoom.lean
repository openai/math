import OAI.Computability.BorderVNP.DiagonalFrozenSignedTask
import OAI.Computability.BorderVNP.DiagonalSignedDescriptionFits

/-! # The two word bounds of the frozen retained-site scanner -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Cover PackedHistoryCircuit.Normalized Filter TeamScales Packing
open TeamContraction TeamContraction.ProcessorSlots RoutingISA RoutingISA.SignedTaskArena

variable {F K : Type} [Field F] [Field K] {D m : ℕ} [NeZero D] {G : PaidIdentity F D m}
    {S : SiteSchedule G} {extra E deg Q A B j : ℕ} (cube : FixedCube K)
    {s : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{0} s (E+1) deg Q A B j)

/-- The actual header of each original opaque report fits one selected word.
The header and body together fit the scanner's source-length operand. These
bounds precede the chart, bundle order, report values and local run. -/
theorem JointSchedule.eventually_frozen_report_scanner_room (headerFactor : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ l size (initial : StartupArena) (dir : Directory.Layout)
        (profile ceiling outputs field : ℕ) (dirs : GeometryDirectories),
      let task := b.frozenSignedTask cube n l size headerFactor initial dir profile ceiling outputs field dirs
      task.p.siteWidth ≤ b.physical.word n ∧ task.p.siteWidth + task.p.bodyCap < 2^b.physical.word n := by
  filter_upwards [b.eventually_signed_description_fit headerFactor,eventually_ge_atTop (2^headerFactor)] with n desc hn
  let r := stretch b.ρ n
  let L := logWidth r n
  have positive : 1≤n := (Nat.one_le_pow _ _ (by decide : 1≤2)).trans hn
  have small : n<2^L := Nat.size_le.mp (CellMacro.Generator.size_le_logWidth n r (stretch_one ..))
  have factor : headerFactor ≤ L := by
    by_contra! less
    exact (hn.trans_lt small).not_ge (Nat.pow_le_pow_right (by decide : 0<2) less.le)
  have Lpos : 1≤L := by
    by_contra! h
    have zero : L=0 := by omega
    rw [zero,pow_zero] at small
    omega
  have words : L ≤ b.physical.word n := Nat.le_self_pow (by omega : E+2 ≠ 0) _
  have wordSquare : L^2 ≤ b.physical.word n :=
    Nat.pow_le_pow_right Lpos (by omega : 2≤E+2)
  intro l size initial dir profile ceiling outputs field dirs task
  constructor
  · exact (Nat.mul_le_mul_right L factor).trans ((pow_two L).symm.le.trans wordSquare)
  · exact ((Nat.le_add_right _ _).trans desc).trans_lt
      (small.trans_le (Nat.pow_le_pow_right (by decide : 0<2) words))

end Diagonal

end BorderVNP
end Computability
end OAI
