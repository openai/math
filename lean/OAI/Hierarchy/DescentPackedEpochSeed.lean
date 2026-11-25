import OAI.Hierarchy.DescentPackedEpochRetained
import OAI.Hierarchy.DescentTerminalPackedSeedFlags

namespace OAI
/-! # Seed validation in the same originally mounted full packed epoch image -/
namespace Hierarchy.DescentPackedEpochShelves
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentSIMDLookup DescentPackedSeed
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Catalyst Computability.BorderVNP.Crossing
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F A : Type} [Field F] {k p : ℕ} (X : Approximation F k p) (R s w : ℕ)
set_option quotPrecheck false
local notation "d" => digitsNeeded s
local notation "M" => DescentPackedSeed.multiplicity w s
local notation "n" => DescentPackedSeed.rows X R s w
local notation "base_" => DescentTerminalPackedSeedFlags.endInput X R s w ([]:List (Source A))
local notation "source_" => DescentTerminalPackedSeedFlags.source X R s w
local notation "rom_" => DescentTerminalPackedSeedFlags.dictionary X R s w ([]:List (Source A))
variable (seed : Select X R s→ A) (z : A→ Bool)
local notation "seedMem" => DescentTerminalPackedSeedFlags.initial X R s w ([]:List (Source A)) seed z

/-- No unpacked epoch array is needed below the seed verdict. -/
def original (lo C r : ℕ) (ss : List (Source A)) := header lo C r ss z seedMem

theorem seed_run (lo C r : ℕ) (ss : List (Source A)) (wide : 2*d ≤ w)
    (seedFits : base_+(n+1) < 2^w) (next : base_+(n+1) ≤ lo) :
    let m:=original X R s w seed z lo C r ss
    let check:=DescentTerminalPackedSeedFlags.check X R s w ([]:List (Source A))
    check.Spec (·=m) (fun _ o=>
      (o (base_+n)=if DescentSeedRoot.valid X (z∘seed) then 0 else 1) ∧
      ∀a,a < base_ ∨ base_+(n+1) ≤ a→ o a=m a) (4+(n+1)*66) ∧ CheapCode check := by
  let m:=original X R s w seed z lo C r ss
  let f:=DescentTerminalPackedSeedFlags.predicate s
  let x:=DescentPackedSeed.cells X (z∘seed)
  have srcSize : n ≤ (source_).size := Nat.le_pow_clog (by decide) n
  have first : (source_).base+(source_).size ≤ base_ := by
    change DescentTerminalPackedSeedFlags.start X R s w ≤ (DescentTerminalPackedSeedFlags.start X R s w+0)+(rom_).size
    omega
  have last : (rom_).base+(rom_).size=base_:=rfl
  have pos : 0 < M:=DescentPackedSeed.multiplicity_pos wide
  have sFit : (source_).Fits w base_:=⟨Nat.two_pow_pos _,by omega,first⟩
  have rFit : (rom_).Fits w base_:=⟨Nat.two_pow_pos _,by omega,last.le⟩
  have prior := DescentTerminalPackedSeedFlags.source_stored X R s w ([]:List (Source A)) seed z
  have src : ∀j : DescentSIMDLookup.Row (Fintype.card (Old X)) (R*8) M,
      m ((source_).base+(row _ _ _ j).val)=((data x j).val:Word w) := by
    intro j
    have small:=(row _ _ _ j).isLt.trans_le srcSize
    exact (frame lo C r ss z seedMem (by omega)).trans (prior j)
  have table:=DescentTerminalPackedSeedFlags.advice_stored X R s w ([]:List (Source A)) seed z
  have read : DescentPackedRejection.Table («M»:=M) f rom_ m := by
    intro h
    have small : h.val < (rom_).size:=h.isLt
    exact (frame lo C r ss z seedMem (by omega)).trans (table h)
  have got:=DescentPackedRejection.run source_ rom_ base_ f x m (by simp [f,DescentTerminalPackedSeedFlags.predicate]) pos
    sFit rFit srcSize rfl seedFits src read
  have works : (∀v j,f (x v j)=0) ↔ DescentSeedRoot.valid X (z∘seed) := by
    simp [f,x,DescentTerminalPackedSeedFlags.predicate,DescentPackedSeed.valid_iff]
  refine ⟨?_, got.2⟩
  refine Procedure.Spec.mono (A := DescentTerminalPackedSeedFlags.check X R s w ([] : List (Source A)))
    got.1 (fun _ h => h) ?_ le_rfl
  intro _ o h
  refine ⟨?_, h.2⟩
  change o (base_ + Fintype.card (Old X) * chunks (R * 8) M) = _
  by_cases valid : DescentSeedRoot.valid X (z ∘ seed)
  · simpa only [ite_eq_left valid, ite_eq_left (works.mpr valid)] using h.1
  · simpa only [ite_eq_right valid, ite_eq_right (mt works.mp valid)] using h.1

/-- The final original seed and profile image has a branch-independent physical
Boolean pin or fixed constant at every addressed word bit. -/
theorem installed_bits (lo C r : ℕ) (ss : List (Source A)) (positive : 0 < r)
    (wide : ∀s∈ss,DescentTerminalEpochBits.width s.C*r ≤ w)
    (a : ℕ) (bound : a < DescentPackedProfileInstall.end_ (lo+extent r ss) C r) (j : Fin (w+1)) :
    let earlier:=fun pos bit=>if h : bit < w+1 then DescentTerminalPackedSeedFlags.pin X R s w ([]:List (Source A))
      seed pos ⟨bit,h⟩ else Sum.inr false
    (headerPin w lo C r ss earlier a j.val).elim z id=(original X R s w seed z lo C r ss a).val.testBit j.val := by
  apply header_pin lo C r ss z seedMem _ _ positive wide bound j.val
  intro i _ b
  by_cases fit : b < w+1
  · rw [dite_eq_left fit]
    exact DescentTerminalPackedSeedFlags.pin_at X R s w ([]:List (Source A)) seed z (by simp) i ⟨b,fit⟩
  · have upper:=(seedMem i).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega : w ≤ b))
    simp [fit,Nat.testBit_lt_two_pow upper]

end
end Hierarchy.DescentPackedEpochShelves

end OAI
