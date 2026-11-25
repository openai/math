import OAI.Computability.NearSquareRoot.KernelEffectiveMixBankLayout

/-! # Packet interface to the effective fixed-coefficient mixer

The two arithmetic rulers are selected from a fixed control header. The
complete header is available again on return, including any recursion
descriptor or shape rulers parked by the caller.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelEffectiveMixBank

open IntegerMultiplication IntegerMultiplication.Code KernelPassMix MixBankLayout

variable {H : Type} [Codec H]
abbrev RowFunction := Tally × List Record → List Record

def replicated (key : H → Rulers) (z : H × Bank) : H × (List Tally × Bank) :=
  (z.1,List.replicate (key z.1).1.length (key z.1).2,z.2)

def finish (i o : ℕ) (f : RowFunction) (z : List Tally × Bank) : Bank :=
  distribute o ((zipFair [] [] (z.1,collect i (ruler z.1,z.2))).map f)

def answer (key : H → Rulers) (i o : ℕ) (f : RowFunction) (z : H × Bank) : H × Bank :=
  (z.1, finish i o f (replicated key z).2)

def expense (key : H → Rulers) (z : H × Bank) : ℕ :=
  size z + ((key z.1).1.length+1)*size (key z.1).2

/-- The chosen command runs with arbitrary parked trees and arbitrary
environments, at a constant independent of the packet and its rulers. -/
def Sound (c : Cmd) (key : H → Rulers) (i o : ℕ) (f : RowFunction) : Prop :=
  ∃ C, ∀ z env, Fits.value env c 0 (send z) (send (answer key i o f z)) (C*(expense key z+1))

open private finish_eq size_replicate from OAI.Computability.NearSquareRoot.KernelPassMixBanks

omit [Codec H] in
theorem answer_bank {α : Type} {i o : ℕ} (key : H → Rulers) (header : H) (l : List α)
    (w : ℕ) (f : RowFunction) (x : α → Fin i → Record) (y : α → Fin o → Record)
    (hk : key header = (tally l.length,tally (w+1)))
    (correct : ∀ a ∈ l, f (tally (w+1),List.ofFn (x a)) = List.ofFn (y a)) :
    answer key i o f (header,bank l x) = (header, bank l y) := by
  apply Prod.ext
  · rfl
  simp only [answer,replicated,hk,tally_length,finish,distribute_exact]
  have hsize : (bank l x).length = i := by simp [bank]
  have align := collect_exact (ruler (List.replicate l.length (tally (w+1)))) (bank l x)
  rw [hsize] at align
  rw [align]
  exact finish_eq ([],[]) ([],[]) f (tally (w+1)) l x y correct

/-- The prepass which makes one copy of the needed arithmetic ruler per address.
Its command is fixed across all matrix dimensions and coefficient tables. -/
theorem prepare (key : H → Rulers) (hk : Code.Easy key) :
    Task (expense key) send (fun z => send (replicated key z)) := by
  let start (z : H × Bank) := (z.1,key z.1,z.2)
  have copy : Code.Easy start := Easy.fst.pair ((Easy.fst.compose hk).pair Easy.snd)
  have gen := ((generate (X := Tally)).on (fun z : H × Bank => key z.1)).left
    (fun z => send z.2)
  have run := gen.right (fun z => send z.1)
  apply (Task.compose copy run).bound 2
  intro z
  simp only [expense]
  change size z + (size z.1 + _) + 1 ≤ 2 * (_ + _ + 1)
  rcases z with ⟨a,b⟩
  simp only [size_prod]
  omega

theorem size_replicated (key : H → Rulers) (z : H × Bank) :
    size (replicated key z) ≤ 3*(expense key z+1) := by
  have p := size_pos (key z.1).2
  have n := Nat.le_mul_of_pos_right (key z.1).1.length p
  rcases z with ⟨a,b⟩
  simp only [replicated,expense,size_prod,size_replicate, Nat.mul_add, Nat.add_mul, Nat.mul_one,
    Nat.one_mul] at *
  omega

end KernelEffectiveMixBank

end NearSquareRoot
end Computability
end OAI
