import OAI.Hierarchy.DescentPackedEpochSeed
import OAI.Hierarchy.DescentPackedRejectionImage

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

def seededState (lo C r : ℕ) (ss : List (Source A)) :=
  DescentPackedRejection.after («M»:=M) base_ (DescentTerminalPackedSeedFlags.predicate s)
    (DescentPackedSeed.cells X (z∘seed)) (original X R s w seed z lo C r ss)

theorem seed_exact_on (lo C r : ℕ) (ss : List (Source A)) (m : Memory w)
    (wide : 2*d ≤ w) (seedFits : base_+(n+1) < 2^w) (next : base_+(n+1) ≤ lo)
    (same : ∀a, a < base_ → m a=original X R s w seed z lo C r ss a) :
    let o:=DescentPackedRejection.after («M»:=M) base_ (DescentTerminalPackedSeedFlags.predicate s)
      (DescentPackedSeed.cells X (z∘seed)) m
    let check:=DescentTerminalPackedSeedFlags.check X R s w ([]:List (Source A))
    check.Exec m o (4+(n+1)*66) ∧ CheapCode check ∧
    (o (base_+n)=0 ↔ DescentSeedRoot.valid X (z∘seed)) ∧
    ∀a,a < base_ ∨ base_+(n+1) ≤ a→ o a=m a := by
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
    exact (same _ (by omega)).trans ((frame lo C r ss z seedMem (by omega)).trans (prior j))
  have table:=DescentTerminalPackedSeedFlags.advice_stored X R s w ([]:List (Source A)) seed z
  have read : DescentPackedRejection.Table («M»:=M) f rom_ m := by
    intro h
    have small : h.val < (rom_).size:=h.isLt
    exact (same _ (by omega)).trans ((frame lo C r ss z seedMem (by omega)).trans (table h))
  have got:=DescentPackedRejection.exact_run source_ rom_ base_ f x m (by simp [f,DescentTerminalPackedSeedFlags.predicate]) pos
    sFit rFit srcSize rfl seedFits src read
  have works : (∀v j,f (x v j)=0) ↔ DescentSeedRoot.valid X (z∘seed) := by
    simp [f,x,DescentTerminalPackedSeedFlags.predicate,DescentPackedSeed.valid_iff]
  have neq:=DescentPackedEpochFold.one_ne (w:=w) (by omega)
  refine ⟨got.1,(seed_run X R s w seed z lo C r ss wide seedFits next).2,?_,got.2.2⟩
  change (DescentPackedRejection.after («M»:=M) base_ f x m
    (base_+Fintype.card (Old X)*chunks (R*8) M)=0 ↔ _)
  rw [got.2.1]
  by_cases pass : DescentSeedRoot.valid X (z∘seed)
  · simp [ite_eq_left (works.mpr pass),pass]
  · simp [ite_eq_right (mt works.mp pass),pass,neq]

theorem seed_exact (lo C r : ℕ) (ss : List (Source A)) (wide : 2*d ≤ w)
    (seedFits : base_+(n+1) < 2^w) (next : base_+(n+1) ≤ lo) :
    let m:=original X R s w seed z lo C r ss
    let o:=seededState X R s w seed z lo C r ss
    let check:=DescentTerminalPackedSeedFlags.check X R s w ([]:List (Source A))
    check.Exec m o (4+(n+1)*66) ∧ CheapCode check ∧
    (o (base_+n)=0 ↔ DescentSeedRoot.valid X (z∘seed)) ∧
    ∀a,a < base_ ∨ base_+(n+1) ≤ a→ o a=m a := by
  exact seed_exact_on X R s w seed z lo C r ss _ wide seedFits next (fun _ _=>rfl)

end
end Hierarchy.DescentPackedEpochShelves

end OAI
