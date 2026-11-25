import OAI.Computability.BorderVNP.CellLocalFactor
import OAI.Computability.BorderVNP.CellTypedRecordSize
import OAI.Computability.BorderVNP.CellPacketInputSize
import OAI.Computability.BorderVNP.CellVisitWidth

/-! # Binary input length and native clock for a single private factor

The local factor call quotes the sweep parameters, the four block fields, the ordinal,
and the actual factor. Its input length is linear in the scalar count and the largest
binary width, including the stored gadget identifiers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet

open ExactQuantumFactoring.BitStackProgram

open private list_length_le port_length_le from OAI.Computability.BorderVNP.CellTypedRecordSize
open private factor_length_le from OAI.Computability.BorderVNP.CellPacketInputSize

private theorem naturals_width (xs : List ℕ) {U : ℕ} (h : ∀ x ∈ xs, x ≤ U) :
    (Typed.naturals xs).length ≤ xs.length*(2*U.size+2)+1 :=
  list_length_le Nat.bits xs U.size fun x hx => by
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (h x hx)

private theorem booleans_width (xs : List Bool) :
    (Typed.booleans xs).length ≤ xs.length*4+1 :=
  list_length_le Procedure.boolCode xs 1 (fun _ _ => le_rfl)

/-- The typed encoding of a factor scales with its transported scalar count,
including every stored gadget ID. -/
theorem typed_factor_length (f : Factor) {U : ℕ} (hf : FactorFields f U) :
    (Typed.factor f).length ≤ 32*(factor f).length*(U.size+1) := by
  cases f with
  | truth ws rs | sign ws rs =>
    obtain ⟨⟨_,hw⟩,_⟩ := hf
    have w := naturals_width ws hw
    have r := booleans_width rs
    simp only [Typed.factor,Typed.factorFields,sumCode,List.length_cons,prodCode,pairBits_length,
      factor,vector,List.length_append,List.length_nil,List.length_map]
    nlinarith only [w,r,Nat.zero_le (ws.length*U.size),Nat.zero_le (rs.length*U.size),
      Nat.zero_le ws.length,Nat.zero_le rs.length,Nat.zero_le U.size]
  | gadget ws rs =>
    obtain ⟨⟨_,hw⟩,hr⟩ := hf
    have w := naturals_width ws hw
    have r := naturals_width rs hr
    simp only [Typed.factor,Typed.factorFields,sumCode,List.length_cons,prodCode,pairBits_length,
      factor,vector,List.length_append,List.length_nil]
    nlinarith only [w,r,Nat.zero_le (ws.length*U.size),Nat.zero_le (rs.length*U.size),
      Nat.zero_le ws.length,Nat.zero_le rs.length,Nat.zero_le U.size]
  | unary i p =>
    obtain ⟨⟨_,hi,hp⟩,_⟩ := hf
    have h := Nat.size_le_size hi
    have hp' := port_length_le p hp
    simp only [Typed.factor,Typed.factorFields,sumCode,List.length_cons,prodCode,pairBits_length,
      Nat.size_eq_bits_len]
    change _ ≤ 32*5*(U.size+1)
    omega

/-- The same typed factor size charged to its one-copy table mass. -/
theorem typed_factor_length_of_mass (f : Factor) {U : ℕ} (hf : FactorFields f U) :
    (Typed.factor f).length ≤ 160*f.staticMass*(U.size+1) := by
  exact (typed_factor_length f hf).trans (by
    calc 32*(factor f).length*(U.size+1) ≤ 32*(5*f.staticMass)*(U.size+1) :=
           Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (factor_length_le f))
         _ = _ := by ring)

/-- A fixed bound for both matrix dimensions bounds the raw one-factor packet. -/
theorem factor_words_of_tableBound (f : Factor) {A : ℕ} (ht : f.TableBound A) :
    (factor f).length ≤ 5*(A+1) := by
  cases f with
  | truth ws rs | sign ws rs | gadget ws rs =>
    obtain ⟨hw,hr⟩ := ht
    simp only [factor,vector,List.length_cons,List.length_append,List.length_nil,List.length_map]
    omega
  | unary i p => change 5 ≤ 5*(A+1); omega

namespace Emit.Local

/-- The three sweep parameters, four block fields and factor ordinal fit in the numeric bound. -/
def ScalarFields (x : Input) (U : ℕ) : Prop :=
  x.1.1.1 ≤ U ∧ x.1.1.2.1 ≤ U ∧ x.1.1.2.2 ≤ U ∧
  x.1.2.1 ≤ U ∧ x.1.2.2.1 ≤ U ∧ x.1.2.2.2.1 ≤ U ∧ x.1.2.2.2.2 ≤ U ∧ x.2.1 ≤ U

/-- Exact local tuple length, with a separator allowance, is bounded by the table
dimension and maximum binary scalar width. -/
theorem code_length (x : Input) {A U : ℕ} (hs : ScalarFields x U)
    (hf : FactorFields x.2.2 U) (ht : x.2.2.TableBound A) :
    (code x).length+1 ≤ 512*(A+1)*(U.size+1) := by
  obtain ⟨s₁,s₂,s₃,s₄,s₅,s₆,s₇,s₈⟩ := hs
  have h := (typed_factor_length x.2.2 hf).trans
    (Nat.mul_le_mul_right (U.size+1) (Nat.mul_le_mul_left 32 (factor_words_of_tableBound x.2.2 ht)))
  simp only [code,paramsCode,fieldsCode,prodCode,pairBits_length,Nat.size_eq_bits_len]
  nlinarith only [h,Nat.size_le_size s₁,Nat.size_le_size s₂,Nat.size_le_size s₃,
    Nat.size_le_size s₄,Nat.size_le_size s₅,Nat.size_le_size s₆,Nat.size_le_size s₇,
    Nat.size_le_size s₈,Nat.zero_le (A*U.size),Nat.zero_le A,Nat.zero_le U.size]

/-- The native printer depends polynomially on the actual binary scalar width.
This applies also to marker IDs whose numerical values exceed a polynomial
in the input order. -/
theorem printer_meter_fields_width (mode : Pass) (A : ℕ) :
    ∃ C j : ℕ, ∀ (x : Input) (U : ℕ),
      ScalarFields x U → FactorFields x.2.2 U → x.2.2.TableBound A →
      (printer mode).meter x ≤ C*(U.size+1)^j := by
  obtain ⟨C,j,hm⟩ := printer_meter mode
  refine ⟨C*(512*(A+1))^j,j,fun x U hs hf ht => ?_⟩
  exact (hm x).trans (by
    calc C*((code x).length+1)^j ≤ C*(512*(A+1)*(U.size+1))^j :=
           Nat.mul_le_mul_left C (Nat.pow_le_pow_left (code_length x hs hf ht) j)
         _ = _ := by rw [mul_pow,Nat.mul_assoc])

/-- A polynomial bound on field widths suffices for one native local factor,
irrespective of the numerical values represented by the marker words. -/
theorem printer_meter_width_scale (mode : Pass) (A B k : ℕ) :
    ∃ C j : ℕ, ∀ (x : Input) (U L : ℕ), U.size+1 ≤ B*(L+1)^k →
      ScalarFields x U → FactorFields x.2.2 U → x.2.2.TableBound A →
      (printer mode).meter x ≤ C*(L+1)^j := by
  obtain ⟨C,j,h⟩ := printer_meter_fields_width mode A
  refine ⟨C*B^j,k*j,fun x U L hscale hs hf ht => ?_⟩
  exact (h x U hs hf ht).trans (by
    calc C*(U.size+1)^j ≤ C*(B*(L+1)^k)^j :=
           Nat.mul_le_mul_left C (Nat.pow_le_pow_left hscale j)
         _ = _ := by rw [mul_pow,pow_mul,Nat.mul_assoc])

/-- A fixed-dimensional local table with polynomially bounded scalar values
takes only polynomial time in the binary size of the order to print on its
actual native stack program. -/
theorem printer_meter_polynomial_fields (mode : Pass) (A B k : ℕ) :
    ∃ C j : ℕ, ∀ (n U : ℕ) (x : Input), U ≤ B*(n+2)^k →
      ScalarFields x U → FactorFields x.2.2 U → x.2.2.TableBound A →
      (printer mode).meter x ≤ C*(n.size+1)^j := by
  obtain ⟨C,j,h⟩ := printer_meter_width_scale mode A (B.size+k+1) 1
  refine ⟨C,j,fun n U x hu hs hf ht => h x U n.size ?_ hs hf ht⟩
  have hwidth := CellMacro.Generator.size_of_polynomial_field hu
  simp only [pow_one,Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one] at hwidth ⊢
  omega

end Emit.Local
end CellSparse.Packet

end BorderVNP
end Computability
end OAI
