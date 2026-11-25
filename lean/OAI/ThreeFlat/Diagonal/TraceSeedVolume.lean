import OAI.ThreeFlat.Diagonal.TraceDiagonalBudget

namespace OAI
/-! # The complete physical H seed adds polynomially many bits and instructions -/

namespace ThreeFlat.Diagonal.TraceStaticRow
open Computability.VPVNP.BurstRAM
variable {F : Type*} [CommRing F] [Fintype F] {u d f : ℕ}

/-- Both the additional public parameter bits and all native initialization instructions
fit one absolute polynomial at the diagonal capacities. -/
theorem seed_volume (_hu : 20000≤u) (cost : 10^26*17^14≤u)
    (hq : Fintype.card F≤u) (hd : d≤15*u^10)
    (hF : Fintype.card F≤2^(16*u^10)) (hw : 3≤16*u^10+1) (hp : u≤2^(16*u^10+1))
    (base : ℕ) (st : Word (16*u^10)) :
    let W := 16*u^10
    let G := gateTable hF hw hp base f st u u d
    let n := G.cells+2*(1+(d+d))
    (2*n)*W+((2*n)*(5*W+6)+6+(4+6*n))≤u^152 := by
  intro W G n
  have gh := diagonal_gateTable (by omega) hq hd hF hw hp base f st
  have g : G.cells≤u^141 := gh.trans (by rw [pow_succ u 140,Nat.mul_comm (u^140) u]; exact Nat.mul_le_mul_right _ cost)
  have pos : 0<u^10 := pow_pos (by omega) _
  have ord : u^10≤u^141 := Nat.pow_le_pow_right (by omega) (by decide)
  have maxN : n≤64*u^141 := by dsimp [n]; omega
  have prod := Nat.mul_le_mul_right (12*W+18) maxN
  have rhs : 64*u^141*(12*W+18)+10≤14000*u^151 := by
    rw [show 151=141+10 by decide,pow_add]
    dsimp [W]
    have h := Nat.mul_le_mul_left (u^141) (show 1≤u^10 by omega)
    nlinarith
  calc
    _ = n*(12*W+18)+10 := by ring
    _ ≤ 64*u^141*(12*W+18)+10 := Nat.add_le_add_right prod _
    _ ≤ 14000*u^151 := rhs
    _ ≤ u^152 := by rw [pow_succ u 151,Nat.mul_comm (u^151) u]; exact Nat.mul_le_mul_right _ (by omega)

end ThreeFlat.Diagonal.TraceStaticRow

end OAI
