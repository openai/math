import OAI.Computability.BorderVNP.CellCQFListMapCost
import OAI.Computability.BorderVNP.CellCQFMeasured

/-! # Metering compact reference lookup on the true input and output table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackProcedure

open _root_.OAI.ExactQuantumFactoring _root_.OAI.ExactQuantumFactoring.BitStackProgram
open _root_.OAI.ExactQuantumFactoring.BitStackProgram.Procedure

variable {A B T I : Type} {ea : A → List Bool} {eb : B → List Bool}
variable {et : T → List Bool} {f : A → B → T}

/-- Mapping compact references costs at most one degree more than the indexed
lookup. The state that stores output prefixes is charged at their true word lengths. -/
theorem measured_listMapWith (d : B) (e : T)
    (p : Procedure (prodCode ea eb) et (fun y => f y.1 y.2))
    (arg : I → A × List B) (s : I → ℕ) {K H : ℕ}
    (hsize : ∀ i, (prodCode ea (listCode eb) (arg i)).length +
      (listCode et ((arg i).2.map (f (arg i).1))).length + 1 ≤ H*(s i+1))
    (hchild : ∀ i, ∀ b ∈ (arg i).2, p.cost ((arg i).1,b) ≤ K*(s i+1)^9) :
    Measured s 10 (listMapWith d e p) arg := by
  obtain ⟨Q,hQ⟩ := cost_listMapWith (ea:=ea) (eb:=eb) et d e
  let R := 3*(H+1)+(H+1)^2
  refine ⟨Q*(H+1)*(K+H^9+R^2+1)+H,fun i => ?_⟩
  let x := arg i
  let t := s i+1
  let a := (prodCode ea (listCode eb) x).length
  let z := (listCode et (x.2.map (f x.1))).length
  let n := x.2.length
  have ht : 1 ≤ t := Nat.succ_le_succ (Nat.zero_le _)
  have hs : a+z+1 ≤ H*t := hsize i
  have hn : n ≤ a := by
    have := list_length_le_code eb x.2
    simp only [n,a,prodCode,pairBits_length]
    omega
  have hz (b : B) (hb : b ∈ x.2) : (et (f x.1 b)).length ≤ z :=
    code_le_of_mem et (List.mem_map_of_mem hb)
  have hcost := hQ p x hz (hchild i)
  have hn' : n+1 ≤ (H+1)*t := by rw [Nat.add_mul,Nat.one_mul]; omega
  have hz' : z+1 ≤ (H+1)*t := by rw [Nat.add_mul,Nat.one_mul]; omega
  have h₁ : a+1 ≤ H*t := by omega
  have ha := Nat.pow_le_pow_left h₁ 9
  rw [Nat.mul_pow] at ha
  have h₂ : t ≤ t^2 := by simpa only [pow_one] using Nat.pow_le_pow_right ht (show 1 ≤ 2 by decide)
  have h₃ : (H+1)*t ≤ (H+1)*t^2 := Nat.mul_le_mul_left _ h₂
  have hprod := Nat.mul_le_mul hn' hz'
  rw [show ((H+1)*t)*((H+1)*t)=(H+1)^2*t^2 by ring] at hprod
  have hspan : tabSpan (prodCode ea (listCode eb)) n x z ≤ R*t^2 := by
    change a+n+(n+1)*(z+1)+1 ≤ (3*(H+1)+(H+1)^2)*t^2
    rw [Nat.add_mul (3*(H+1)) ((H+1)^2),Nat.mul_assoc 3 (H+1)]
    have hR : H*t ≤ (H+1)*t := Nat.mul_le_mul_right t (by omega)
    omega
  have hsp := Nat.pow_le_pow_left hspan 2
  rw [Nat.mul_pow,← pow_mul] at hsp
  have h₄ : t^(2*2) ≤ t^9 := Nat.pow_le_pow_right ht (by decide)
  have hsp' := hsp.trans (Nat.mul_le_mul_left _ h₄)
  have ht' : 1 ≤ t^9 := Nat.one_le_pow _ _ ht
  have hv : K*t^9+(a+1)^9+(tabSpan (prodCode ea (listCode eb)) n x z)^2+1 ≤
      (K+H^9+R^2+1)*t^9 := by
    simp only [Nat.add_mul,Nat.one_mul]
    omega
  have hfin := hcost.trans (Nat.mul_le_mul (Nat.mul_le_mul_left Q hn') hv)
  change _ ≤ Q*((H+1)*t)*((K+H^9+R^2+1)*t^9) at hfin
  rw [show Q*((H+1)*t)*((K+H^9+R^2+1)*t^9)=Q*(H+1)*(K+H^9+R^2+1)*t^10 by ring] at hfin
  change (listMapWith d e p).cost x+a+z+1 ≤ (Q*(H+1)*(K+H^9+R^2+1)+H)*t^10
  rw [Nat.add_mul]
  have ht₁ : t ≤ t^10 := by simpa only [pow_one] using Nat.pow_le_pow_right ht (show 1 ≤ 10 by decide)
  have hw := hs.trans (Nat.mul_le_mul_left H ht₁)
  omega

end StackProcedure

end BorderVNP
end Computability

namespace ExactQuantumFactoring.BitStackProgram.Procedure

export OAI.Computability.BorderVNP.StackProcedure (
  measured_listMapWith)

end ExactQuantumFactoring.BitStackProgram.Procedure
end OAI
