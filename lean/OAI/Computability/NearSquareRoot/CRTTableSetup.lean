import OAI.Computability.NearSquareRoot.BoxProgram
import OAI.Computability.NearSquareRoot.CRTTablePhysical

/-! # Generating a CRT level's lookup tables from the address width -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication.Code

/-- Width, level, and the complete serial control setting suffice to generate
the box and all lookup tables. The bit selects inverse routing. -/
abbrev SetupQuery := Bool × Tally × Tally × List Bool

def setupTables (s : SetupQuery) :=
  levelTables (s.1, s.2.1, BoxProgram.encoded s.2.2.1, s.2.2.2)

theorem setupTables_poly : Poly setupTables := by
  have h := (show Poly (fun s : SetupQuery => s.2.2.1) by fun_prop).compose BoxProgram.encoded_poly
  exact ((show Poly (fun s : SetupQuery => s.1) by fun_prop).pair
    ((show Poly (fun s : SetupQuery => s.2.1) by fun_prop).pair (h.pair (by fun_prop)))).compose
    levelTables_poly

structure RawSetting where
  k : ℕ
  depth : ℕ
  bits : List Bool
  inverse : Bool
  depth_le : depth ≤ k
  bit_count : bits.length ≤ k

def RawSetting.raw (s : RawSetting) : SetupQuery := (s.inverse,tally s.depth,tally s.k,s.bits)

private theorem rawSize : Dom RawSetting.k (fun i => size i.raw) := by
  refine ⟨1, 12, fun s => ?_⟩
  have hd := s.depth_le
  have hb := s.bit_count
  simp only [RawSetting.raw, size_prod, size_bit, size_tally, tally_length, IntegerMultiplication.Bits.size_word, pow_one]
  omega

/-- A single finite multitape program performs the parameter search and
then emits the full level's tables. Both its trace length and the number of
visited cells are polynomial in the address width, for all control settings. -/
theorem generatedMachine : PolyTreeMachine RawSetting.k
    (fun s => send s.raw) (fun s => send (setupTables s.raw)) :=
  polyTreeMachine_of_BT (setupTables_poly.on rawSize) rawSize

/-- The callable version returns every parked register tape and head exactly
as it found it. The polynomial covers the box search as well as the tables. -/
theorem generatedCall :
    ∃ degree : ℕ, ShortWord.PhysicalTask (fun s : RawSetting => (s.k+1)^degree)
      (fun s => send s.raw) (fun s => send (setupTables s.raw)) := by
  obtain ⟨cost, ⟨deg,C,h⟩, task⟩ := setupTables_poly.on rawSize
  refine ⟨deg, ShortWord.physicalTask (task.bound (C+1) ?_)⟩
  intro s
  specialize h s
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

end CRTTable

end NearSquareRoot
end Computability
end OAI
