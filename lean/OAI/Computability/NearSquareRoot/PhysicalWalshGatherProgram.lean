import OAI.Computability.NearSquareRoot.PhysicalWalshGrouped
import OAI.Computability.NearSquareRoot.CRTPositionDescriptor

/-! # Conjugating the physical grouped Walsh pass by bit-position routing

The input controller supplies both orientations of the compact routing table.
The return table is parked throughout the forward routing and the grouped
Walsh pass. All three commands share the ordered-list record encoding.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GatherProgram

open IntegerMultiplication Code Space FixedPoint Controlled.Reflections

variable {I : Type}

/-- Natural-address presentation of an input, with zeroes past the last address. -/
def lift {k : ℕ} (x : Fin (2^k) → Record k) (n : ℕ) := if h : n < 2^k then x ⟨n,h⟩ else 0

@[simp] theorem lift_fin {k : ℕ} (x : Fin (2^k) → Record k) (i : Fin (2^k)) : lift x i = x i := by
  simp [lift,i.isLt]

theorem lift_words {k : ℕ} (x : Fin (2^k) → Record k) :
    Pieces.words (2^k) (lift x) = Odd.words x := by simp [Pieces.words_ofFn,Odd.words]

abbrev Header := (Tally × Tally) × Table × Table

/-- Both lookup tables use least-significant-bit positions, in source-to-target order. -/
def control {k : ℕ} (s : ℕ) (p : Equiv.Perm (Fin k)) : Header :=
  ((tally k,tally s),table p,table p.symm)

private abbrev R := List Dusk.Pair
private def prepare (v : Header × R) := ((v.1.2.1,v.2),(v.1.1,v.1.2.2))
private def middle (v : R × (Tally × Tally) × Table) := ((v.2.1,v.1),v.2.2)
private def restore (v : R × Table) := (v.2,v.1)
private theorem easy_prepare : Easy prepare := by unfold prepare; fun_prop
private theorem easy_middle : Easy middle := by unfold middle; fun_prop
private theorem easy_restore : Easy restore := by unfold restore; fun_prop

noncomputable def beginCmd : Cmd := easy_prepare.choose
noncomputable def middleCmd : Cmd := easy_middle.choose
noncomputable def restoreCmd : Cmd := easy_restore.choose
theorem table_volume {k : ℕ} (p : Equiv.Perm (Fin k)) : size (table p) ≤ 2*Odd.volume k := by
  refine (table_size p).trans ?_
  rw [pow_two,Odd.volume]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ Nat.lt_two_pow_self)

theorem row_volume {k : ℕ} (x : Fin (2^k) → Record k) : size (Odd.words x) ≤ 400*Odd.volume k + 1 := by
  rw [← lift_words,Pieces.words_size]
  unfold Odd.volume componentBits; ring_nf; omega

/-- Compose the physical address permutation, the original-size grouped
program, and the inverse address permutation. The arrays `x`, `u`, `v`, `y`
are the exact inputs and outputs of those three physical calls. -/
theorem conjugate (k s : I → ℕ) (hs : ∀ i,s i ≤ k i) (p : (i : I) → Equiv.Perm (Fin (k i)))
    (x u v y : (i : I) → Fin (2^k i) → Record (k i)) (t r tg rg : I → ℕ)
    (forward : BoundedTask t r (fun i => send (table (p i),Odd.words (x i))) (fun i => send (Odd.words (u i))))
    (grouped : BoundedTask tg rg (fun i => send ((tally (k i),tally (s i)),Odd.words (u i)))
      (fun i => send (Odd.words (v i))))
    (reverse : BoundedTask t r (fun i => send (table (p i).symm,Odd.words (v i))) (fun i => send (Odd.words (y i)))) :
    BoundedTask (fun i => t i+tg i+Odd.volume (k i)) (fun i => max (r i) (rg i)+Odd.volume (k i))
      (fun i => send (control (s i) (p i), Odd.words (x i))) (fun i => send (Odd.words (y i))) := by
  let h i := control (s i) (p i)
  let a i := (h i,Odd.words (x i))
  let b i := (Odd.words (u i),((h i).1,(h i).2.2))
  let c i := (Odd.words (v i),(h i).2.2)
  have beginRun := BoundedTask.of_time ((show Easy prepare from ⟨beginCmd,easy_prepare.choose_spec⟩).on a)
  have middleRun := BoundedTask.of_time ((show Easy middle from ⟨middleCmd,easy_middle.choose_spec⟩).on b)
  have endRun := BoundedTask.of_time ((show Easy restore from ⟨restoreCmd,easy_restore.choose_spec⟩).on c)
  have chain := ((((beginRun.compose (forward.left (fun i => send ((h i).1,(h i).2.2)))).compose
    middleRun).compose (grouped.left (fun i => send (h i).2.2))).compose endRun).compose reverse
  apply chain.bound 1300 1000 <;> intro i
  all_goals
    have kv : k i+1 ≤ Odd.volume (k i) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    have small : size (h i).1 ≤ 4*Odd.volume (k i)+3 := by
      have := hs i; simp only [h,control,size_prod,size_tally,tally_length]; omega
    have f := table_volume (p i)
    have g : size (h i).2.2 ≤ 2*Odd.volume (k i) := table_volume (p i).symm
    have aSize : size (a i) ≤ 410*Odd.volume (k i)+8 := by
      change (size (h i).1+(size (table (p i))+size (h i).2.2+1)+1)+size (Odd.words (x i))+1 ≤ _
      have := row_volume (x i); omega
    have parked : size ((h i).1,(h i).2.2) ≤ 6*Odd.volume (k i)+4 := by
      change size (h i).1+size (h i).2.2+1 ≤ _; omega
    have bSize : size (b i) ≤ 410*Odd.volume (k i)+6 := by
      change size (Odd.words (u i))+size ((h i).1,(h i).2.2)+1 ≤ _; have := row_volume (u i); omega
    have cSize : size (c i) ≤ 405*Odd.volume (k i)+3 := by
      change size (Odd.words (v i))+size (h i).2.2+1 ≤ _; have := row_volume (v i); omega
  · change size (a i)+t i+size (b i)+tg i+size (c i)+t i+1 ≤ _
    omega
  · change max (max (max (max (max (size (a i)+size (a i)) (r i+size ((h i).1,(h i).2.2)))
      (size (b i)+size (b i))) (rg i+size (h i).2.2)) (size (c i)+size (c i))) (r i)+1 ≤ _
    omega

end PhysicalWalsh.GatherProgram

end NearSquareRoot
end Computability
end OAI
