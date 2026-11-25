import OAI.Computability.NearSquareRoot.PhysicalWalshXorRowEnds
import OAI.Computability.NearSquareRoot.PhysicalWalshXorOpcodeCommand

/-! # Compiling an opcode on an arbitrary number of high prefix rows

The two boundary programs are fixed once on the entire opcode/input world.
Subsequent choices of native program, subfamily, and resource reserves do
not change either boundary program.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow

open IntegerMultiplication Code Adic Strip Staff Loom Packed
open Controlled Controlled.PositionProgram XorReserve NamedPacked
open CommonRegisters GeneratorSyntax Filter

variable {X : Type} (r : Regime X) (P k : X → ℕ) (hP : Realizes r P) (hk : Realizes r k)
    {U : X → Type} (u : (x:X) → Series (U x)) (op : X → Op)
    (f : (x:X) → Input (P x) (k x) (U x))

noncomputable def windowCmd (native : Cmd) :=
  let ends := rowEnds r P k hP hk u f (rewired P k op f)
  opcodeCmd ends.choose ends.choose_spec.choose native

theorem windowCmd_effective {I : Type} [Primcodable I] {native : I → Cmd} (h : Effective ltr native) :
    Effective ltr (fun i => windowCmd r P k hP hk u op f (native i)) := opcodeCmd_effective _ _ h

theorem windowCmd_within : ∀ᶠ R : ℕ in atTop, ∀ n, Within R n → Within R (windowCmd r P k hP hk u op f n) :=
  opcodeCmd_within _ _

theorem opcodeOnNamed {native : Cmd} {ρ : ℝ} (row : NativeRowAt r P k hP u native ρ op f) :
    ∃ D, OpcodeAt r P k u op f ρ D (windowCmd r P k hP hk u op f native) := by
  let ends := rowEnds r P k hP hk u f (rewired P k op f)
  exact opcodeOnNamedWith r P k hP u op f (e:=ends.choose_spec.choose_spec.choose)
    ends.choose_spec.choose_spec.choose_spec row

/-- Pay for a fixed shortfall in the low reserve by enlarging the accounting
for each physical row cell. The underlying data and compiled command are identical. -/
theorem OpcodeAt.withReserveMargin {ρ : ℝ} {D : ℕ} {cmd : Cmd} (stage : OpcodeAt r P k u op f ρ D cmd)
    {Y:Type} (s : Y→X) (B m Q factor : Y→ℕ) (margin : ℕ)
    (lengths : ∀y, (u (s y)).count ≤ pack (B y) (m y)) (scale : ∀y, r.scale (s y) ≤ Q y)
    (pos : ∀y, 0 < m y) (low : ∀y,payloadBits D (Q y) ≤ B y+margin)
    (rate : ∀y,2*Spindle.modes k (τ:=ρ) (s y) ≤ factor y) (high : ∀y,factor y ≤ 2^P (s y)) :
    let V y := volume (P (s y)) (k (s y)) (B y) (m y)
    EffectiveBoundedTask.Runs cmd (fun y => V y*(factor y+1)) V
      (fun y => .fork (r.header (s y)) (store (u (s y)) (f (s y))))
      (fun y => store (u (s y)) (rewired P k op f (s y))) := by
  intro V
  let C := 2^margin
  have cap y : pack (B y) (m y) ≤ pack (B y+margin) (m y) :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..))
  have run := stage s (fun y => B y+margin) m Q factor (fun y => (lengths y).trans (cap y)) scale pos low rate high
  have vol y : volume (P (s y)) (k (s y)) (B y+margin) (m y) = C*V y := by
    dsimp only [C,V,XorReserve.volume]
    rw [←Nat.add_assoc,pow_add]
    ring
  have absAux (n a : ℕ) : n*a+1 ≤ (n+1)*(a+1) := by rw [Nat.succ_mul,Nat.mul_succ]; omega
  have absorb := absAux C
  apply run.bound (C+1) (C+1) <;> intro y
  · change volume _ _ _ _*(factor y+1)+1 ≤ _
    rw [vol,Nat.mul_assoc]
    exact absorb _
  ·
    rw [vol]
    exact absorb _

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
