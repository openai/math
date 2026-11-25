import OAI.Computability.NearSquareRoot.PhysicalWalshXorReserve
import OAI.Computability.NearSquareRoot.PhysicalWalshXorSweep
import OAI.Computability.NearSquareRoot.CRTPositionOpcodeStage
import OAI.Computability.NearSquareRoot.CRTPositionGuardRuler

/-! # Executing native address instructions between two spectator fields -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic
open IntegerMultiplication.Strip IntegerMultiplication.Staff IntegerMultiplication.Loom
open IntegerMultiplication.Packed NearSquareRoot.Space NearSquareRoot.Controlled
open NearSquareRoot.Controlled.PositionProgram XorReserve

/-- A physical cell carries the low spectators and all bits of their records. -/
noncomputable def cell {P k : ℕ} {U : Type} (u : Series U)
    (f : (Fin k → Bool) → Block 2 P → U → Bead) (a : Block 2 (P+k)) : Tree :=
  let z := (prefixView (rfl : P+k=P+k)).cast.symm a
  strip u (f (prefixBit z.2) z.1)

noncomputable def store {P k : ℕ} {U : Type} (u : Series U)
    (f : (Fin k → Bool) → Block 2 P → U → Bead) : Tree := stripe (line 2 (P+k)) (cell u f)

@[simp] theorem cell_at {P k : ℕ} {U : Type} (u : Series U)
    (f : (Fin k → Bool) → Block 2 P → U → Bead) (a : Block 2 P) (b : Block 2 k) :
    cell u f ((prefixView rfl).cast (a,b)) = strip u (f (prefixBit b) a) := by simp [cell]

theorem cell_size {P k : ℕ} {U : Type} (u : Series U)
    (f : (Fin k → Bool) → Block 2 P → U → Bead) (a) : (cell u f a).count ≤ 2*u.count+1 :=
  bulk _ _

theorem store_size {P k B m : ℕ} {U : Type} (u : Series U)
    (f : (Fin k → Bool) → Block 2 P → U → Bead) (h : u.count ≤ pack B m) (hm : 0 < m) :
    (store u f).count ≤ 5*volume P k B m := by
  have h₁ := stripe_size (line 2 (P+k)) (cell u f) _ (cell_size u f)
  rw [lineSize] at h₁
  have h₂ : 0 < pack B m := Nat.mul_pos (Nat.two_pow_pos _) hm
  have h₃ := Nat.mul_le_mul_left (2^(P+k)) (show 2*u.count+1+1 ≤ 4*pack B m by omega)
  have h₄ : 0 < 2^(P+k)*pack B m := Nat.mul_pos (Nat.two_pow_pos _) h₂
  change (store u f).count ≤ _ at h₁
  rw [show volume P k B m = 2^(P+k)*pack B m by simp only [XorReserve.volume,XorReserve.pack,pow_add,mul_assoc]]
  rw [Nat.mul_left_comm] at h₃
  omega

/-- The workspace degree is fixed before choosing the family of legal reserves. -/
theorem opcodeOn {ρ : ℝ} (dispatch : OpFamily ρ id)
    {X : Type} {r : Regime X} (P k : X → ℕ) (op : X → Op)
    (hP : Realizes r P) (hk : Realizes r k) (hop : r.Has op)
    (ok : ∀ x, WellFormed (k x) (guardWidth (k x)) (op x))
    {U : X → Type} (u : (x:X) → Series (U x)) (l : X → ℕ) (hu : ∀ x, (u x).count ≤ l x)
    (f : (x:X) → (Fin (k x) → Bool) → Block 2 (P x) → U x → Bead) :
    ∃ D : ℕ, ∀ {Y : Type} (select : Y → X) (B m Q factor : Y → ℕ),
      (∀ y, l (select y) = pack (B y) (m y)) → (∀ y, r.scale (select y) ≤ Q y) →
      (∀ y, 0 < m y) → (∀ y, payloadBits D (Q y) ≤ B y) →
      (∀ y, 2*Spindle.modes k (τ:=ρ) (select y) ≤ factor y) → (∀ y, factor y ≤ 2^P (select y)) →
      let V y := volume (P (select y)) (k (select y)) (B y) (m y)
      BoundedTask (fun y => V y*(factor y+1)) V
        (fun y => .fork (r.header (select y)) (store (u (select y)) (f (select y))))
        (fun y => store (u (select y)) (f (select y) ∘ fun b =>
          act (guardWidth (k (select y))) b (op (select y)))) := by
  let Z := (x:X) × Block 2 (P x)
  let g (x:X) := f x ∘ fun b => act (guardWidth (k x)) b (op x)
  let rr := fixedRowRegime r P hP
  have h₁ : Realizes rr (fun z:Z => k z.1) := fixedRowGlobal P hP hk
  have h₂ : rr.Has (fun z:Z => op z.1) := fixedRowGlobal P hP hop
  have step := dispatch (fun z:Z => k z.1) (fun z:Z => op z.1) h₁ h₂ (fun z => ok z.1)
    (fun z => u z.1) (fun z => hu z.1) (fun z b => f z.1 (prefixBit b) z.2)
  change Breeze _ rr _ (fun z:Z => l z.1)
    (fun z => .fork (rr.header z) (stripe (line 2 (k z.1)) fun b =>
      strip (u z.1) (f z.1 (prefixBit b) z.2)))
    (fun z => stripe (line 2 (k z.1)) fun b =>
      strip (u z.1) (f z.1 (prefixBit (nativeOp (k z.1) (guardWidth (k z.1)) (op z.1) b)) z.2)) at step
  have row : Breeze (Spindle.modes (fun z:Z => k z.1) (τ:=ρ)) rr
      (fun z => (line 2 (k z.1)).count) (fun z => l z.1)
      (fun z => .fork (rr.header z) (stripe (line 2 (k z.1)) fun b =>
        cell (u z.1) (f z.1) ((prefixView rfl).cast (z.2,b))))
      (fun z => stripe (line 2 (k z.1)) fun b =>
        cell (u z.1) (g z.1) ((prefixView rfl).cast (z.2,b))) := by
    simpa only [cell_at,g,Function.comp_apply,nativeOp_bits] using step
  obtain ⟨D,run⟩ := packedWindowRowsOn P k (fun x => P x+k x) hP hk (fun _ => prefixView rfl)
    (fun x => cell (u x) (f x)) (fun x => cell (u x) (g x)) row
  refine ⟨D,fun select B m Q factor counts scale pos low hrs high => ?_⟩
  have cap y := (hu (select y)).trans_eq (counts y)
  exact run select B m Q factor (fun y _ => (lineSize ..).le) (fun y _ => counts y)
    (fun y a => (cell_size _ _ a).trans (by have := cap y; omega))
    (fun y a => (cell_size _ _ a).trans (by have := cap y; omega)) scale pos low (fun y _ => hrs y) high

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
