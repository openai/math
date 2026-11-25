import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalMaskNative
import OAI.Computability.NearSquareRoot.InterchangeRequestHeader

/-! # A computable row-linear price for selected-field mask commands -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Mask

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  IntegerMultiplication.Port InterchangeAddress InterchangeROMAddress Space

open private request request_layout from OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalMaskNative

private theorem poly_exp (D : ℕ) : ∃ A : ℕ, ∀ x : ℕ, (x+1)^D ≤ A*2^x := by
  obtain ⟨t,ht⟩ := Filter.eventually_atTop.1 (Param.beats 1 D)
  refine ⟨t^D+2,fun x => ?_⟩
  by_cases hx : t ≤ x+1
  · have h := ht (x+1) hx
    rw [Nat.one_mul,pow_succ] at h
    rw [Nat.add_mul]
    omega
  · have h := Nat.pow_le_pow_left (show x+1 ≤ t by omega) D
    exact h.trans ((by omega : t^D ≤ t^D+2).trans
      (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))))

/-- A bound on the two literal cuts and the runtime header in terms of the
number of address digits, retaining the symbolic template dimensions. -/
theorem shape_power (D : ℕ) : ∃ A : ℕ, ∀ {J : Type} [DecidableEq J] {n b : ℕ}
    (ord : J ≃ Fin n) (j : J) (P G B : Tape) (_ : 2 ≤ b)
    (_ : ∀ k ∈ P ++ G ++ B, 2 ≤ k ∧ k ≤ b) (f : ℕ),
    (size (parameter b n (ord j).val,header f P G B)+1)^D ≤
      ((4*b+8*n+24)^D*A) * (arrays ord (line b f) P G B).count := by
  obtain ⟨A,hA⟩ := poly_exp D
  refine ⟨A,?_⟩
  intro J inst n b ord j P G B hb ok f
  let : NeZero b := ⟨by omega⟩
  let r := request ord P G B b f j
  let a : Request b := ⟨P,G,B,f,1,fun _ => .atom false⟩
  have ar : Request.Admissible r := by
    apply Request.admissible_inherited hb ok
    intro k hk
    simp only [r,request,preamble_false,silence_false_true,appendix_true, List.mem_append] at hk
    rcases hk with (((hp | hr) | (hr | hg | hr)) | (hr | hs))
    · exact .inr (by simp [hp])
    · exact .inl (source_radix _ _ _ _ hr)
    · exact .inl (source_radix _ _ _ _ hr)
    · exact .inr (by simp [hg])
    · exact .inl (source_radix _ _ _ _ hr)
    · exact .inl (source_radix _ _ _ _ hr)
    · exact .inr (by simp [hs])
  have hd : a.digits ≤ r.digits := by
    simp only [a,r,request,Request.digits,preamble_false,silence_false_true,appendix_true,
      List.length_append]
    omega
  have hs := (Request.header_count_le a ok).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hd 1))
  change size (header f P G B) ≤ (2*b+8)*(r.digits+1) at hs
  have hq : size (parameter b n (ord j).val) ≤ 2*b+8*n+14 := by
    simp only [parameter,InterchangeROMMaskCompile.numeric,size_prod,size_tally,tally_length]
    have hj := (ord j).isLt
    omega
  have hd0 : 0 < r.digits+1 := by omega
  have hq' := hq.trans (Nat.le_mul_of_pos_right _ hd0)
  have hc : size (parameter b n (ord j).val,header f P G B)+1 ≤
      (4*b+8*n+24)*(r.digits+1) := by
    simp only [size_prod,Nat.add_mul,Nat.mul_assoc] at *
    omega
  have hp := Request.pow_digits_le r hb ar
  have hn := (request_layout (b:=b) ord P G B f j).1
  calc
    _ ≤ ((4*b+8*n+24)*(r.digits+1))^D := Nat.pow_le_pow_left hc _
    _ = (4*b+8*n+24)^D*(r.digits+1)^D := Nat.mul_pow ..
    _ ≤ (4*b+8*n+24)^D*(A*2^r.digits) := Nat.mul_le_mul_left _ (hA r.digits)
    _ = ((4*b+8*n+24)^D*A)*2^r.digits := (Nat.mul_assoc ..).symm
    _ ≤ _ := Nat.mul_le_mul_left _ (hp.trans hn.le)

/-- An explicit multiplier in the varying template parameters. -/
def linearPrice (C D A b n : ℕ) : ℕ := C*((4*b+8*n+24)^D*A+2)

theorem computable_linearPrice {X : Type} [Primcodable X] {b n : X → ℕ}
    (C D A : ℕ) (hb : Computable b) (hn : Computable n) :
    Computable fun x => linearPrice C D A (b x) (n x) := by
  have h : Computable fun x => 4*b x+8*n x+24 :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 4) hb)
      (Primrec.nat_mul.to_comp.comp (Computable.const 8) hn)) (Computable.const 24)
  have hp (k : ℕ) : Computable fun x => (4*b x+8*n x+24)^k := by
    induction k with
    | zero => simpa using (Computable.const (α := X) 1)
    | succ k ih =>
      simpa only [pow_succ] using Primrec.nat_mul.to_comp.comp ih h
  exact Primrec.nat_mul.to_comp.comp (Computable.const C) (Primrec.nat_add.to_comp.comp
    (Primrec.nat_mul.to_comp.comp (hp D) (Computable.const A)) (Computable.const 2))

/-- With native admissible radices, all three resources are linear in the
physical record count, with one computable multiplier for each template. -/
theorem command_linear :
    ∃ C D A : ℕ, ∀ {J : Type} [DecidableEq J] {n b : ℕ} (ord : J ≃ Fin n) (j : J)
      (P G B : Tape) (_ : 2 ≤ b) (_ : ∀ k ∈ P ++ G ++ B, 2 ≤ k ∧ k ≤ b)
      (f : ℕ) (env : Env) (deck : Deck) (base : ℕ), DeckCap base deck →
      let w := linearPrice C D A b n*(arrays ord (line b f) P G B).count
      BoundedFits env (command b n (ord j).val) (pile 0 (send (header f P G B)) deck)
        (pile 0 (maskRow (b:=b) ord P G B f j) deck) w (base+w) w := by
  obtain ⟨C,D,run⟩ := command_bounded
  obtain ⟨A,price⟩ := shape_power D
  refine ⟨C,D,A,?_⟩
  intro J inst n b ord j P G B hb ok f env deck base hd
  let N := (arrays ord (line b f) P G B).count
  let H := size (parameter b n (ord j).val,header f P G B)+1
  have hc : H^D ≤ ((4*b+8*n+24)^D*A)*N := price ord j P G B hb ok f
  have pos : 0 < N := by
    by_contra! h
    have z : N=0 := by omega
    have t : 0 < H^D := Nat.pow_pos (by dsimp [H]; omega)
    simp only [z,Nat.mul_zero] at hc
    omega
  have hp : solid P := fun k hk => (ok k (by simp [hk])).1
  have hg : solid G := fun k hk => (ok k (by simp [hk])).1
  have hs : solid B := fun k hk => (ok k (by simp [hk])).1
  have hh : C*(N+H^D+1) ≤ linearPrice C D A b n*N := by
    rw [linearPrice,Nat.mul_assoc,Nat.add_mul]
    exact Nat.mul_le_mul_left _ (by omega)
  exact (run ord j P G B hb hp hg hs f env deck base hd).mono hh
    (Nat.add_le_add_left hh _) hh

end InterchangeROMRepair.Physical.Mask

end NearSquareRoot
end Computability
end OAI
