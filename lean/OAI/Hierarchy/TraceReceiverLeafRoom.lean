import OAI.Hierarchy.TraceSeedCharge
import OAI.ThreeFlat.Diagonal.TraceBucketImage
import OAI.ThreeFlat.RAM.TraceBucketImageSize

namespace OAI
/-! # Uniform native operand bounds for every selected verifier leaf -/

namespace Hierarchy.TraceReceiverLeafRoom

open ThreeFlat Diagonal TraceBitHeader RAM Computability.VPVNP.BurstRAM PrivateRAM
open Filter TraceDistribution TraceBucketAtom
open scoped Classical

variable (F : Type) [Field F] [Fintype F]

noncomputable def coefficient (copies : ℕ) :=
  (2*(copies+1)+3*Fintype.card ((Fin 3→Bool)→F)+65+256+10^26)*65^14

/-- The live operand size of a leaf is its grid row count times a fixed
polynomial in w. Scratch bank origins never enter this polynomial. -/
theorem footprint {w pc regs slots S base q low fuel : ℕ} (M : Machine (64*w) pc regs slots)
    (fit : NativeTrace.Fits M S base ((q+1)+low) fuel) (hF : Fintype.card F ≤ 2^(64*w)) (st : Word (64*w))
    (copies raw dict masks ids : ℕ) (hf : Fintype.card F ≤ 64*w) (hp : pc≤64*w) (hr : regs≤64*w)
    (hk : slots≤64*w) (hd : (q+1)+low≤64*w) :
    let B := bucketShape (q:=q) (low:=low) (S:=S) (f:=fuel) hF fit.width fit.labels base st regs slots copies raw dict masks ids
    B.footprint ≤ 200*2^((q+1)+low)*(coefficient F copies*(w+1)^14+1)^3 := by
  intro B
  let x := 64*w+1
  let c := 2*(copies+1)+3*Fintype.card ((Fin 3→Bool)→F)+65+256+10^26
  let n := coefficient F copies*(w+1)^14
  have h1 : 1 ≤ x^14 := one_le_pow₀ (show 1 ≤ x by dsimp only [x]; omega)
  have hx : x ≤ x^14 := by simpa using (Nat.pow_le_pow_right (by dsimp [x]; positivity : 0<x) (by decide : 1≤14))
  have hpow : x^14 ≤ 65^14*(w+1)^14 := by
    rw [←mul_pow]
    apply Nat.pow_le_pow_left
    dsimp [x]; omega
  have grow (a : ℕ) (ha : a ≤ c) : a*x^14≤n := by
    calc
      _ ≤ c*(65^14*(w+1)^14) := Nat.mul_le_mul ha hpow
      _ = _ := by dsimp [n,coefficient,c]; ring
  have small {a : ℕ} (ha : a ≤ c) : a≤n := (Nat.le_mul_of_pos_right _ h1).trans (grow a ha)
  have xd : (q+1)+low ≤ n := hd.trans ((show 64*w≤x by dsimp [x];omega).trans
    (hx.trans (by simpa using grow 1 (by dsimp [c];omega))))
  have gates := (native_cells M fit hF st hf hp hr hk hd).trans (grow (10^26) (by dsimp [c];omega))
  have step := (native_stride M fit hF st hf hp hr hk hd).trans (grow (256+10^26) (by dsimp [c];omega))
  have lib : B.equalId+B.zeroId+B.unitId ≤ 3*Fintype.card ((Fin 3→Bool)→F) := by
    have h₁ : B.equalId<Fintype.card ((Fin 3→Bool)→F) := Fin.isLt _
    have h₂ : B.zeroId<Fintype.card ((Fin 3→Bool)→F) := Fin.isLt _
    have h₃ : B.unitId<Fintype.card ((Fin 3→Bool)→F) := Fin.isLt _
    omega
  apply footprint_le B (small (by dsimp [c];omega)) (Nat.two_pow_pos _) _ xd (by change low≤n; omega) _ gates
    (small (by change (copies+1)*2≤c; dsimp [c];omega)) step (lib.trans (small (by dsimp [c];omega)))
  · apply Nat.pow_le_pow_right (by decide)
    change low≤(q+1)+low
    omega
  · change S+fuel≤2*2^((q+1)+low)
    simpa [pow_add] using fit.grid

omit [Field F] in
theorem eventual_margin (copies : ℕ) : ∀ᶠ w : ℕ in atTop, ∀ d : ℕ, d ≤ 2*w+1 →
    200*2^d*(coefficient F copies*(w+1)^14+1)^3 < 2^(4*w+2) ∧
    5*(4*w+2)+128 ≤ 64*w := by
  let C := coefficient F copies
  filter_upwards [polynomial_room (200*(C+1)^3) 42,eventually_ge_atTop 4] with w poly hw
  intro d hd
  have one : 1 ≤ (w+1)^14 := one_le_pow₀ (by omega)
  have extra : C*(w+1)^14+1 ≤ (C+1)*(w+1)^14 := by nlinarith
  have localSize : 200*(C*(w+1)^14+1)^3 ≤ 2^(w/100) := by
    calc
      _ ≤ 200*((C+1)*(w+1)^14)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left extra _)
      _ = (200*(C+1)^3)*(w+1)^42 := by ring
      _ ≤ _ := poly
  refine ⟨?_,by omega⟩
  calc
    _ = 2^d*(200*(C*(w+1)^14+1)^3) := by dsimp [C]; ring
    _ ≤ 2^d*2^(w/100) := Nat.mul_le_mul_left _ localSize
    _ = 2^(d+w/100) := (pow_add ..).symm
    _ < 2^(4*w+2) := Nat.pow_lt_pow_right (by decide) (by omega)


end Hierarchy.TraceReceiverLeafRoom

end OAI
