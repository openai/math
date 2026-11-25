import OAI.Computability.BorderVNP.RoutingISALink
import OAI.Computability.BorderVNP.RoutingOffsets

/-!
# Physical address fragments of the fixed team evaluator

The frame carries the local team number, processor count and field widths.
The first private word of each processor is its literal. Exterior fields are
listed by increasing partner, with the local team omitted. The extra pin field
follows them. A physical block concatenates the `ℓlink` bits of each processor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- Address of flat block position in the actual initialization memory. -/
def physicalBitAddress (team teams literal link partner pos : ℕ) : ℕ :=
  let stride := 2*literal + (teams-1)*link
  let rank := if partner < team then partner else partner-1
  pos/link * stride + literal + rank*link + pos%link

/-- The processor and offset are the quotient and remainder in a nonempty block.
The address stays inside the exterior part of this processor's input. -/
theorem physicalBitAddress_bounds {team teams literal link partner pos processors : ℕ}
    (ht : team < teams) (hp : partner < teams) (hd : partner ≠ team) (hl : 0 < link)
    (hpos : pos < processors*link) :
    let stride := 2*literal + (teams-1)*link
    pos/link < processors ∧ pos/link*stride + literal ≤ physicalBitAddress team teams literal link partner pos ∧
    physicalBitAddress team teams literal link partner pos < pos/link*stride + literal + (teams-1)*link := by
  have hrank : (if partner < team then partner else partner-1) < teams-1 := by split <;> omega
  have hr := Nat.mod_lt pos hl
  have hh := Nat.mul_le_mul_right link (Nat.succ_le_of_lt hrank)
  rw [Nat.succ_mul] at hh
  dsimp only [physicalBitAddress]
  exact ⟨(Nat.div_lt_iff_lt_mul hl).mpr hpos, by omega, by omega⟩

/-- Input registers 30 and 31 name the physical partner and flat block position.
The emitted instructions return the true shared-memory bit address in register
48. Registers 0 through 29 are preserved. -/
def physicalAddress : Code := .block [
  readFrame 36 62 63 0, readFrame 37 62 63 1,
  readFrame 38 62 63 4, readFrame 39 62 63 3,
  .constant 51 1, .constant 52 2,
  .binary .sub 53 37 51, .binary .mul 53 53 38,
  .binary .mul 54 39 52, .binary .add 53 53 54,
  .binary .div 48 31 38, .binary .mul 48 48 53, .binary .add 48 48 39,
  .ifLt 30 36 (.copy 54 30) (.binary .sub 54 30 51),
  .binary .mul 54 54 38, .binary .add 48 48 54,
  .binary .mod 54 31 38, .binary .add 48 48 54]

/-- Address of an oriented pair entry in a row-major public table. -/
def pairAddress (out first second teams base : Reg) : Code := .block [
  .binary .mul out first teams, .binary .add out out second, .binary .add out out base]

/-- Address of a three-index entry in a row-major public table. -/
def tripleAddress (out first second third teams base : Reg) : Code := .block [
  .binary .mul out first teams, .binary .add out out second, .binary .mul out out teams,
  .binary .add out out third, .binary .add out out base]

/-- Address of one two-hop leg. Inputs are endpoint, relay, opposite endpoint
and local quotient in registers 32–35. The calling team may be either endpoint
of the physical block. Register 48 is the returned word address. -/
def legAddress : Code := .block [
  readFrame 36 62 63 0, readFrame 37 62 63 1, readFrame 40 62 63 5,
  readFrame 41 62 63 18, readFrame 42 62 63 17,
  tripleAddress 46 32 33 34 37 42, .load 31 46, .binary .add 31 31 35,
  .binary .add 31 31 40,
  .ifLt 33 32 (.block [pairAddress 46 33 32 37 41, .load 47 46, .binary .add 31 31 47]) .nop,
  .ifEq 36 32 (.copy 30 33) (.copy 30 32), physicalAddress]

/-- Fixed-word code for the ordinal skip at one endpoint. -/
def skipRegister (value missing one : Reg) : Code :=
  .ifLt value missing .nop (.binary .add value value one)

/-- Endpoint-side address of ordinal `j` in the unordered demand list to the
partner team. Input registers are 30 (other endpoint) and 31 (ordinal).
The result is in register 48. Registers 0–29 are preserved. -/
def endpointAddress : Code := .block [
  readFrame 32 62 63 0, readFrame 37 62 63 1, .copy 34 30,
  .constant 51 1, .constant 52 2, .binary .sub 53 37 52,
  .binary .div 35 31 53, .binary .mod 33 31 53,
  .ifLt 32 34 (.block [skipRegister 33 32 51, skipRegister 33 34 51])
    (.block [skipRegister 33 34 51, skipRegister 33 32 51]),
  legAddress]

end RoutingISA

end BorderVNP
end Computability
end OAI
