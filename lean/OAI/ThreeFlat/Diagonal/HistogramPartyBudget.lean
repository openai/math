import OAI.ThreeFlat.Diagonal.HistogramPartyNetwork
import OAI.ThreeFlat.Diagonal.MotifNativeCompactors
import OAI.ThreeFlat.Diagonal.HistogramPartyArithmetic

namespace OAI
/-! # Width-uniform charge for the complete local histogram network -/

namespace ThreeFlat.Diagonal.HistogramTileNetwork

open LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector MotifOuterTerms MotifOrderedCells MotifNativeCompactors
open scoped BigOperators Classical

variable {J E S H F : Type*} [CommRing F] [Fintype J] [Nonempty J] [Fintype E] [Fintype S]
  [Fintype H] [DecidableEq H] [Nonempty H] {k e n d r h : ℕ}
  (D : PortGraph J E) (G : Supply J S) (j : J) (base : E → ℕ)
  (B : Header (D.Port j) H (fun p => base p.1.1) k n)
  (portsAt : Fin e ≃ (ports G).Port j) (sw : H → S → ℕ) (fits : ∀ z a, sw z (portsAt a).1.1 ≤ d)
  (M : ∀ z v, D.State (fun a => Fin (2^base a)) v → (ports G).State (fun a => Fin (2^sw z a)) v → F)
  (id : H ≃ Fin h) (v : Histogram H r)

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] in
/-- Physical rows and private bits of both the selector and payload networks. -/
theorem partyNetwork_size :
    let m := siteHeight r d
    let N := partyNetwork D G j base B portsAt sw fits M id v
      (partialInput F (r*d) m) (partialInput F r m)
    N.cells + N.internal ≤ (r+1)*partyCoefficient B.arity k h e d*(m+1)^3 := by
  let m := siteHeight r d
  let C := partialInput F r m
  let K := tile D G j base B portsAt sw fits M
  let A := admissionNetwork G j portsAt id B.code C v
  let c := 2^m*(32000*(m+1)^3)
  have hC : h*C.cells ≤ h*c := Nat.mul_le_mul_left _ (partialInput_rows (F:=F) r m)
  have iC : h*C.internal ≤ h*c := Nat.mul_le_mul_left _ (partialInput_bits (F:=F) r m)
  have hA : A.cells + A.internal ≤ r*(2^(e*k+h)*(e*k+h+2)) + r*h + 2*(h*c) := by
    dsimp only [A,admissionNetwork]
    rw [MotifSelectorChecks.network_cells,MotifSelectorChecks.network_hidden]
    simp only [Nat.mul_add,Nat.mul_one,Nat.mul_two] at *
    omega
  have hK := tile_size K r m
  have both := Nat.add_le_add hA hK
  apply le_trans _ (absorb_party_charge r d h e (2^(e*k+h)*(e*k+h+2))
    (2^(B.arity+(e*d+e*d))*(B.arity+(e*d+e*d)+2)))
  dsimp only [partyNetwork]
  rw [BitNetwork.Ordered.pair_cells,BitNetwork.Ordered.pair_hidden]
  change A.cells + (K.network (partialInput F (r*d) m)).cells +
    (A.internal + (K.network (partialInput F (r*d) m)).internal) ≤ _
  calc
    _ = (A.cells + A.internal) + ((K.network (partialInput F (r*d) m)).cells +
        (K.network (partialInput F (r*d) m)).internal) := by ac_rfl
    _ ≤ _ := both

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] in
/-- The charge used by the greedy replay tick budget. -/
theorem partyNetwork_charge :
    let m := siteHeight r d
    let N := partyNetwork D G j base B portsAt sw fits M id v
      (partialInput F (r*d) m) (partialInput F r m)
    10000*(N.cells+N.internal) ≤
      (r+1)*(10000*partyCoefficient B.arity k h e d)*(m+1)^3 := by
  have q := Nat.mul_le_mul_left 10000 (partyNetwork_size D G j base B portsAt sw fits M id v)
  simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using q

end ThreeFlat.Diagonal.HistogramTileNetwork

end OAI
