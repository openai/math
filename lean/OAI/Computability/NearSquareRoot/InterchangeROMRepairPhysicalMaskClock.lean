import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalMaskEmit
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalMaskPrice

/-! # A computable row-linear clock for the persistent repair mask -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMMaskCompile

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  IntegerMultiplication.Port Space CommonRegisters GeneratorSyntax InterchangeROMAddress
  InterchangeROMTable InterchangeROMRepair InterchangeROMRepair.Physical

def factor (C m : ℕ) (pos : List ℕ) :=
  (52+C)*m + 60 + 6*m + C + maskRowFactor pos + 20

theorem price_bound (C D b n m : ℕ) (h : Header) (pos : List ℕ) (N : ℕ) :
    price C D b n m h pos N ≤ factor C m pos * (N+(height b n h+1)^(D+1)+1) := by
  let u := height b n h+1
  let V := N+u^(D+1)+1
  have one : 1 ≤ V := Nat.le_add_left _ _
  have posu : 0 < u := by dsimp [u]; omega
  have grow : u^D ≤ u^(D+1) := Nat.pow_le_pow_right posu (Nat.le_succ D)
  have hu : u ≤ u^(D+1) := by simpa only [pow_one] using
    (Nat.pow_le_pow_right posu (by omega : 1 ≤ D+1))
  have len : size h ≤ V := by dsimp only [V]; dsimp only [u,height] at hu; dsimp only [u,height]; omega
  have vu : N+u^D+1 ≤ V := by dsimp only [V]; omega
  have vn : N+1 ≤ V := by dsimp only [V]; omega
  have cost := Nat.mul_le_mul_left C vu
  have term : 45*size h + C*(N+u^D+1)+7 ≤ (52+C)*V := by
    rw [Nat.add_mul]
    omega
  calc
    _ ≤ ((52+C)*V)*m + 60*V + (6*V)*m + C*V + maskRowFactor pos*V + 20*V := by
      unfold price
      change (45*size h+C*(N+u^D+1)+7)*m + _ + _ + _ + _ + _ ≤ _
      gcongr <;> omega
    _ = _ := by unfold factor; change _ = _*V; ring

private theorem double_header (b n j : ℕ) (h : Header) (hj : j<n) :
    height b n h+1 ≤ 2*(size (Mask.parameter b n j,h)+1) := by
  simp only [height,Mask.parameter,numeric,size_prod,size_tally,tally_length]
  omega

def linearFactor (C D A b n m : ℕ) (pos : List ℕ) :=
  factor C m pos * (2^(D+1)*((4*b+8*n+24)^(D+1)*A)+2)

theorem computable_linearFactor {X : Type} [Primcodable X] (C D A : ℕ)
    {b n m : X → ℕ} {pos : X → List ℕ} (hb : Computable b) (hn : Computable n)
    (hm : Computable m) (hp : Computable pos) :
    Computable fun x => linearFactor C D A (b x) (n x) (m x) (pos x) := by
  have front : Computable fun x => factor C (m x) (pos x) :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp
      (Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp
        (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const _) hm)
          (Computable.const 60)) (Primrec.nat_mul.to_comp.comp (Computable.const 6) hm))
        (Computable.const C)) (computable_maskRowFactor hp)) (Computable.const 20)
  have base : Computable fun x => 4*b x+8*n x+24 :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 4) hb)
      (Primrec.nat_mul.to_comp.comp (Computable.const 8) hn)) (Computable.const 24)
  have pw : Computable₂ (fun (x k : ℕ) => x^k) :=
    (KernelComputableAddress.primrec_pow Primrec.fst Primrec.snd).to₂.to_comp
  exact Primrec.nat_mul.to_comp.comp front (Primrec.nat_add.to_comp.comp
    (Primrec.nat_mul.to_comp.comp (Computable.const _) (Primrec.nat_mul.to_comp.comp
      (pw.comp base (Computable.const (D+1))) (Computable.const A)))
    (Computable.const 2))

/-- Admissible tapes absorb the full header polynomial into their native
address volume. The constant A depends only on the degree. -/
theorem price_le (D : ℕ) :
    ∃ A : ℕ, ∀ (C m : ℕ) (bits : List ℕ) {J : Type} [DecidableEq J] {n b : ℕ}
      (ord : J ≃ Fin n) (_ : J) (P G B : Tape) (_ : 2 ≤ b)
      (_ : ∀ k ∈ P ++ G ++ B, 2 ≤ k ∧ k ≤ b) (f : ℕ),
      let rows := arrays ord (line b f) P G B
      price C D b n m (header f P G B) bits rows.count ≤ linearFactor C D A b n m bits*rows.count := by
  obtain ⟨A,sh⟩ := Mask.shape_power (D+1)
  refine ⟨A,?_⟩
  intro C m bits J dec n b ord slot P G B hb ok f
  let h := header f P G B
  let rows := arrays ord (line b f) P G B
  let N := rows.count
  let j := (ord slot).val
  let u := size (Mask.parameter b n j,h)+1
  let F := ((4*b+8*n+24)^(D+1)*A)
  have hs : u^(D+1) ≤ F*N := sh ord slot P G B hb ok f
  have nh : N>0 := by
    by_contra! z
    have zero : N=0 := by omega
    have pos : 0<u^(D+1) := Nat.pow_pos (by dsimp [u]; omega)
    simp [zero] at hs
  have h2 := double_header b n j h (ord slot).isLt
  have hh := (Nat.pow_le_pow_left h2 (D+1)).trans (show (2*u)^(D+1) ≤ 2^(D+1)*(F*N) by
    rw [Nat.mul_pow]
    exact Nat.mul_le_mul_left _ hs)
  have bound := price_bound C D b n m h bits N
  apply bound.trans
  unfold linearFactor
  rw [Nat.mul_assoc,Nat.add_mul]
  apply Nat.mul_le_mul_left
  change N+_+1 ≤ (2^(D+1)*F)*N+2*N
  rw [Nat.mul_assoc]
  omega

/-- For admissible spectator shapes the entire controller fits a number of
steps and stack cells linear in the actual number of physical addresses. -/
theorem emit_linear :
    ∃ C D A : ℕ, ∀ {J : Type} [DecidableEq J] {n b m : ℕ} (ord : J ≃ Fin n)
      (cols : Series (Fin m)) (chooseSlot : Fin m → J) (scaffold : Fin m) (P G B : Tape)
      (_ : 2 ≤ b) (_ : ∀ k ∈ P ++ G ++ B, 2 ≤ k ∧ k ≤ b) (f : ℕ) (env : Env)
      deck base, DeckCap base deck →
      let ranks := cols.tab fun j => (ord (chooseSlot j)).val
      let bits := cols.tab Fin.val
      let rows := arrays ord (line b f) P G B
      let w := linearFactor C D A b n m bits*rows.count
      BoundedFits env (emit b n ranks (cols.explore.idxOf scaffold) bits)
        (pile 0 (send (header f P G B)) deck) (pile 0 (stripe rows fun a =>
          numeral (Raw.mask (fun j => decide (number (a.2.2.2.1 (chooseSlot j)) <
            number (a.2.1 (chooseSlot j))))).val) deck) w (base+w) w := by
  obtain ⟨C,D,run⟩ := emit_bounded
  obtain ⟨A,pr⟩ := price_le D
  refine ⟨C,D,A,?_⟩
  intro J dec n b m ord cols chooseSlot scaffold P G B hb ok f env deck base hd
  have mono := pr C m (cols.tab Fin.val) ord (chooseSlot scaffold) P G B hb ok f
  have hp : solid P := fun k hk => (ok k (by simp [hk])).1
  have hg : solid G := fun k hk => (ok k (by simp [hk])).1
  have he : solid B := fun k hk => (ok k (by simp [hk])).1
  exact (run ord cols chooseSlot scaffold P G B hb hp hg he f env deck base hd).mono mono
    (Nat.add_le_add_left mono base) mono

end InterchangeROMMaskCompile

end NearSquareRoot
end Computability
end OAI
