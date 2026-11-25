import OAI.Optimization.LinearProgramming.RAM.Code
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! The statically visible address-register writes of a structured RAM block. An indirect
address-bank store conservatively allows arbitrary register changes. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM

structure AddressWrites where
  indirect : Bool
  direct : Finset ℕ
  deriving DecidableEq

def AddressWrites.join (a b : AddressWrites) : AddressWrites :=
  ⟨a.indirect || b.indirect, a.direct ∪ b.direct⟩

def AddressWrites.Avoids (w : AddressWrites) (p : ℕ) : Prop := w.indirect = false ∧ p ∉ w.direct

private theorem avoids_join (a b : AddressWrites) (p : ℕ) :
    (a.join b).Avoids p ↔ a.Avoids p ∧ b.Avoids p := by
  simp [AddressWrites.join, AddressWrites.Avoids, and_assoc, and_left_comm]

def Instr.addressWrites : Instr → AddressWrites
  | .addrConst d _ | .addrCopy d _ | .incr d _ | .decr d _ | .addrLoad d _ => ⟨false,{d}⟩
  | .addrStore _ _ => ⟨true,∅⟩
  | _ => ⟨false,∅⟩

def Block.addressWrites : Block → AddressWrites
  | .skip => ⟨false,∅⟩
  | .op i => i.addressWrites
  | .seq a b | .branch _ a b => a.addressWrites.join b.addressWrites
  | .loop _ a => a.addressWrites

private theorem instruction_address_frame {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (i : Instr) (s t : State K) (p : ℕ) (hi : i.addressWrites.Avoids p)
    (hr : execInstr i s = some t) : t.index p = s.index p := by
  cases i <;> simp [Instr.addressWrites, AddressWrites.Avoids] at hi
  all_goals simp only [execInstr] at hr
  all_goals try split at hr
  all_goals cases hr
  all_goals simp_all [State.putData, State.putIndex]

/-- An address outside the block's write footprint survives every terminating execution. -/
theorem Block.Eval.address_frame {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {safe : Memory K → Prop} {b : Block} {m t : Memory K} {k : ℕ}
    (run : Block.Eval safe b m k t) (p : ℕ) (h : b.addressWrites.Avoids p) : t.index p = m.index p := by
  induction run with
  | skip => rfl
  | op _ _ op => exact instruction_address_frame _ _ _ p h (op 0)
  | seq _ _ ia ib =>
    rcases (avoids_join _ _ _).mp h with ⟨ha,hb⟩
    exact (ib hb).trans (ia ha)
  | branchTrue _ _ ih => exact ih ((avoids_join _ _ _).mp h).1
  | branchFalse _ _ ih => exact ih ((avoids_join _ _ _).mp h).2
  | loopFalse => rfl
  | loopTrue _ _ _ ib il => exact (il h).trans (ib h)

/-- Keep the ordered list as well, so that a closed block's footprint can be checked by
kernel evaluation without deciding equality between quotient multisets. -/
def Instr.directAddressList : Instr → List ℕ
  | .addrConst d _ | .addrCopy d _ | .incr d _ | .decr d _ | .addrLoad d _ => [d]
  | _ => []

def Block.directAddressList : Block → List ℕ
  | .skip => []
  | .op i => i.directAddressList
  | .seq a b | .branch _ a b => a.directAddressList ++ b.directAddressList
  | .loop _ a => a.directAddressList

theorem Block.directAddressList_toFinset (b : Block) : b.directAddressList.toFinset = b.addressWrites.direct := by
  induction b with
  | skip => rfl
  | op i => cases i <;> simp [directAddressList, Instr.directAddressList, addressWrites, Instr.addressWrites]
  | seq _ _ ha hb | branch _ _ _ ha hb => simp [directAddressList, addressWrites, AddressWrites.join, ha, hb]
  | loop _ _ h => exact h

/-- Check the finite write set with a boolean predicate chosen by the caller. -/
theorem Block.Eval.address_frame_of_list {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {safe : Memory K → Prop} {b : Block} {m t : Memory K} {k : ℕ}
    (run : Block.Eval safe b m k t) (f : ℕ → Bool) (hind : b.addressWrites.indirect = false)
    (hcheck : b.directAddressList.all f = true) (p : ℕ) (hp : f p = false) : t.index p = m.index p := by
  apply run.address_frame
  refine ⟨hind, ?_⟩
  intro hmem
  rw [← b.directAddressList_toFinset, List.mem_toFinset] at hmem
  have htrue := List.all_eq_true.mp hcheck p hmem
  simp_all

end RAM
end LinearProgramming
end Optimization
end OAI
