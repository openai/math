import Mathlib.Data.Nat.Log
import OAI.Hierarchy.ProtocolRAMScan
import OAI.ThreeFlat.RAM.PhysicalInputPhases

namespace OAI
/-! # The one-dimensional static row-to-counter offset table -/

namespace Hierarchy.ProtocolRAMPackedRanked

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM
open scoped Fin.CommRing
variable {W : ℕ}

def groupBits (groups : ℕ) := Nat.log 2 (groups+1)+1
def biasBank (start groups : ℕ) : Bank := ⟨start,groupBits groups⟩
def mountBias (start groups menu : ℕ) (m : Memory W) : Memory W :=
  fillSegment start (2^groupBits groups) (fun a=>(((a-start)*(menu+1):ℕ):Word W)) m

theorem bias_read (start groups menu : ℕ) (m : Memory W) (a : Word W) :
    (biasBank start groups).read (mountBias start groups menu m) a=
      (((a.val%(2^groupBits groups))*(menu+1):ℕ):Word W) := by
  have small := Nat.mod_lt a.val (Nat.two_pow_pos (groupBits groups))
  simp [biasBank,Bank.read,Bank.size,mountBias,fillSegment,small]

theorem bias_frame (start groups menu : ℕ) (m : Memory W) (a : ℕ)
    (outside : a < start ∨ start+2^groupBits groups ≤ a) : mountBias start groups menu m a=m a := by
  simp [mountBias,fillSegment,show ¬ (start ≤ a ∧ a < start+2^groupBits groups) by omega]

theorem group_capacity (groups : ℕ) : groups≤2^groupBits groups := by
  exact (Nat.le_succ groups).trans (Nat.lt_pow_succ_log_self (by decide) (groups+1)).le

theorem bias_words (groups : ℕ) : 2^groupBits groups≤2*(groups+1) := by
  have h := Nat.pow_log_le_self 2 (show groups+1≠0 by omega)
  rw [groupBits,pow_succ]
  omega

end Hierarchy.ProtocolRAMPackedRanked

end OAI
