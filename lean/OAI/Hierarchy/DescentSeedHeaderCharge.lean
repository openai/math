import OAI.Hierarchy.DescentSeedPackedHeaderNumbers
import OAI.Hierarchy.DescentPackedRegroup
import OAI.Hierarchy.DescentInitialPackage

namespace OAI
/-! # True size of the grouped seed census and its shared saturation bank -/
namespace Hierarchy
open Catalyst DescentSeedRoot DescentInitialHost DescentTerminalEpochChart
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)
local notation "V₀" => Fintype.card (Vertex X)
local notation "H" => Fintype.card (Old X)

namespace DescentPackedSeed
theorem grouped_multiplicity {w s : ℕ} (wide : 16*digitsNeeded s≤w) :
    multiplicity w s=DescentSIMDLookup.lanes w (8*digitsNeeded s)*8 := by simp [multiplicity,wide]

def headerWords (R s w : ℕ) := publicWords X+rows X R s w

omit [Field F] in
theorem invoice (R s w : ℕ) (wide : 2*digitsNeeded s≤w) :
    headerWords X R s w*w≤publicWords X*w+H*w+4*H*(R*8)*digitsNeeded s := by
  unfold headerWords
  rw [Nat.add_mul]
  change publicWords X*w+(H*DescentSIMDLookup.chunks (R*8) (multiplicity w s))*w≤_
  by_cases grouped : 16*digitsNeeded s≤w
  · have width:2*(8*digitsNeeded s)≤w:=by omega
    have pos:= (DescentSIMDLookup.occupancy w (8*digitsNeeded s) (by have:=Nat.zero_lt_succ s.log2;unfold digitsNeeded;omega) width).1
    rw [grouped_multiplicity grouped,DescentSIMDLookup.chunks_group R _ 8 pos (by decide)]
    have bound:=DescentSIMDLookup.volume H R w (8*digitsNeeded s) (by unfold digitsNeeded;positivity) width
    nlinarith only [bound]
  · have packed:=DescentSIMDLookup.volume H (R*8) w (digitsNeeded s) (Nat.zero_lt_succ _) wide
    simpa only [multiplicity,ite_eq_right grouped,Nat.add_assoc] using Nat.add_le_add_left packed (publicWords X*w)

theorem public_bound : publicWords X≤6+80*(X.size+1) := by
  have bill:=(DescentInitialHost.«initialize» X).2.1
  change V₀+Fintype.card (Cable X)+Fintype.card (Port p X.width) ≤ 10*(X.size+1) at bill
  unfold publicWords
  omega

/-- Bit budget at the approximation's own copy-network size. The only
full-width rows proportional to the original graph are immutable. -/
theorem startup_bits (R s w : ℕ) (wide : 2*digitsNeeded s≤w) :
    headerWords X R s w*w≤(6+90*(X.size+1))*w+320*(X.size+1)*R*digitsNeeded s := by
  have sub : H≤V₀ := Fintype.card_le_of_embedding ⟨Sum.inl,Sum.inl_injective⟩
  have bill := (DescentInitialHost.«initialize» X).2.1
  change V₀+Fintype.card (Cable X)+Fintype.card (Port p X.width) ≤ 10*(X.size+1) at bill
  have small : H≤10*(X.size+1) := by omega
  have hw := Nat.mul_le_mul_right w small
  have hs := Nat.mul_le_mul_right (R*digitsNeeded s) small
  have fixed:=Nat.mul_le_mul_right w (public_bound X)
  nlinarith only [invoice X R s w wide,hw,hs,fixed]

end DescentPackedSeed

namespace DescentTerminalPackedSeedFlags
variable {A : Type} (R s w : ℕ)
local notation "M" => DescentPackedSeed.multiplicity w s
local notation "d" => digitsNeeded s
local notation "N" => DescentPackedSeed.rows X R s w

omit [Field F] in
theorem price (wide : 2*d ≤ w) : (4+(N+1)*66)*w ≤
    70*(w+Fintype.card (Old X)*w+4*Fintype.card (Old X)*(R*8)*d) ∧ 2^(d*M) ≤ 2^(w/2) := by
  have packed:=DescentPackedSeed.invoice X R s w wide
  rw [DescentPackedSeed.headerWords,Nat.add_mul] at packed
  have rows : N*w ≤ H*w+4*H*(R*8)*d := by omega
  refine ⟨?_,Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) ?_⟩
  · nlinarith only [rows,Nat.zero_le (H*w),Nat.zero_le (H*(R*8)*d)]
  · by_cases grouped : 16*d ≤ w
    · rw [DescentPackedSeed.grouped_multiplicity grouped]
      calc
        d*(DescentSIMDLookup.lanes w (8*d)*8) = DescentSIMDLookup.lanes w (8*d)*(8*d) := by ring
        _ ≤ _ := DescentSIMDLookup.lanes_fit w (8*d)
    · rw [DescentPackedSeed.multiplicity,ite_eq_right grouped,Nat.mul_comm]
      exact DescentSIMDLookup.lanes_fit w d

omit [Field F] in
/-- Full fixed header extent includes the compact census, the reserved
physical selector rows, and the single shared saturation table. -/
theorem header_extent (ts : List (Source A)) (wide : 2*d ≤ w) :
    endInput X R s w ts ≤
      2*DescentPackedSeed.headerWords X R s w+1+DescentTerminalEpochHeader.extent ts+2^(w/2) := by
  have rows := DescentDyadicSpan.span_le N
  have dictionarySize := (price X R s w wide).2
  change DescentPackedSeed.publicWords X+DescentDyadicSpan.span N+DescentTerminalEpochHeader.extent ts+
    2^(d*M) ≤ 2*(DescentPackedSeed.publicWords X+N)+1+DescentTerminalEpochHeader.extent ts+2^(w/2)
  omega

end DescentTerminalPackedSeedFlags
end
end Hierarchy

end OAI
