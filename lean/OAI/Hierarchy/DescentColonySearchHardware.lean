import OAI.Hierarchy.DescentColonySelectionRAM
import OAI.Hierarchy.DescentColonyCandidateHardware

namespace OAI
/-! # ROM, register and instruction costs of the full multiplier selection -/

noncomputable section
namespace Hierarchy
open ProtocolRAM DescentColonies
open DescentColonies.CandidateRAM (Bounded)
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open DescentGL (Bits)
variable {G H k : ℕ}

theorem DescentFirstMinimumRAM.code_bound (w out : ℕ) (b : Bank) (keys : List ℕ) :
    Bounded (DescentFirstMinimumRAM.code w out b keys) (DescentFirstMinimumRAM.ticks out b keys) := by
  induction keys with
  | nil =>
    refine ⟨scan_cheap w out 0 (.lit 0),?_⟩
    change 15≤4*4
    decide
  | cons i is ih =>
    exact CandidateRAM.seq_bound ih (CandidateRAM.scan_bound _ _ 1 _ (by decide))

namespace DescentColonies.AllSeedsRAM

theorem search_bounded (w base D cap : ℕ) (a : Bits k) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ) :
    Bounded (search w base D cap a incoming ptr).1 (search w base D cap a incoming ptr).2 := by
  apply CandidateRAM.seq_bound
  · apply CandidateRAM.seq_bound
    · apply CandidateRAM.batch_bound (steps w base D cap a incoming ptr)
      intro i
      exact CandidateRAM.candidate_bound w (slot G H k base i.val) incoming ptr D cap a (seedAt k i)
    · exact CandidateRAM.scan_bound _ _ _ _ (Nat.two_pow_pos _)
  · exact DescentFirstMinimumRAM.code_bound ..

theorem search_cheap (w base D cap : ℕ) (a : Bits k) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ) :
    CheapCode (search w base D cap a incoming ptr).1 := (search_bounded w base D cap a incoming ptr).cheap

theorem search_size (w base D cap : ℕ) (a : Bits k) (incoming : Fin H→List (Fin H)) (ptr : Fin G→Fin H→ℕ) :
    let P := search w base D cap a incoming ptr
    P.1.labels+P.1.registers+P.1.slots≤4*P.2 := (search_bounded w base D cap a incoming ptr).size

end DescentColonies.AllSeedsRAM
end Hierarchy

end
end OAI
