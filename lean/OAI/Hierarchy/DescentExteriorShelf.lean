import OAI.Hierarchy.DescentExteriorShelfStore
import OAI.Hierarchy.DescentPublicExteriorRelocation
import OAI.Hierarchy.DescentExteriorShelfNumbers
import OAI.Hierarchy.DescentExteriorVerifiedRows
import Mathlib.Data.Nat.Log

namespace OAI
/-! # A common memory layout for all three literal exterior routing passes -/
namespace Hierarchy.DescentExteriorShelf
open DescentExterior DescentExteriorFetch DescentGL Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section

variable (j r t e origin : ℕ)
local notation "B" => bank j r t e origin
local notation "H" => span j r t e

/-- Source and destination ordinals, the selected matrix, both payload
orders for the hidden bits, and the immutable ROM occupy disjoint banks. -/
def keyBanks : KeyBanks := ⟨B 0,B 1,B 2,B 3⟩
def gatherBanks (s : Fin 3) : Banks := ⟨B 17,B 4,B (5+s.val),B 8,B (9+s.val),B (12+s.val)⟩
def guesses (s : Fin 2) : Bank := B (15+s.val)
def keyAt := origin+17*H
def start := origin+18*H
def endAt := start j r t e origin+3*rows j r e

/-- The full memory includes each dictionary once and only a constant
number of padded rows per genuine exterior chunk. -/
theorem price {w : ℕ} (room : tableBits j r t≤w/2) :
    endAt j r t e origin ≤ origin+39*rows j r e+18*(1+2^(w/2)) := by
  have h:=span_price j r t e room
  unfold endAt start
  omega

theorem fit_to {bits i z : ℕ} (left : i<z) (room : origin+(z+1)*H<2^bits) :
    (B i).Fits bits (origin+z*H) := by
  have pos : 0<H := Nat.two_pow_pos _
  have one := Nat.mul_le_mul_right H (show 1≤z+1 by omega)
  have moved := Nat.mul_le_mul_right H (Nat.succ_le_of_lt left)
  simp only [Bank.Fits,bank,Bank.size]
  change 0<H ∧ H<2^bits ∧ origin+i*H+H≤origin+z*H
  rw [Nat.succ_mul] at moved
  omega

end
end Hierarchy.DescentExteriorShelf

end OAI
