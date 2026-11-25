import OAI.Computability.NearSquareRoot.PhysicalWalshPositionIndex
import OAI.Computability.NearSquareRoot.PhysicalWalshGatherProgram
import OAI.Computability.NearSquareRoot.PrecisionDigitCloth

/-! # Ordered fixed-point records in the native position permuter

Each record travels as one film containing both component words. Their equal
lengths let the receiver retrieve the split point by halving the film's ruler.
The native permutation therefore requires one linear conversion at either end.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.PositionCloth

open IntegerMultiplication Code Adic Packed Strip Loom FixedPoint Space
open Controlled Controlled.PositionProgram Controlled.Reflections
noncomputable section

abbrev filmRows {k : ℕ} (x : Fin (2^k) → Record k) := (Odd.words x).map Dusk.tie

/-- Recover the two component words from a film with equal-length halves. -/
def untie (l : Dusk.Film) : Dusk.Pair := cutLists ((Carry.half (ruler l)).1,l.map notify)

theorem easy_untie : Easy untie := by
  unfold untie
  apply easy_cut
  exact ((Easy.ruler Easy.identity).compose Carry.halfCost).fstCompose.pair (Easy.finite notify).mapping

@[simp] theorem untie_mark {w : ℕ} (x : Dusk.Grain w) : untie (Dusk.tie (Dusk.mark x)) = Dusk.mark x := by
  have half : (Carry.half (ruler (Dusk.tie (Dusk.mark x)))).1 = ruler (Dusk.mark x).1 := by
    rw [Carry.half_v,ruler_length,Dusk.film]
    change tally (2*(w+1)/2) = ruler (Dusk.mark x).1
    rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    convert recover_tally (ruler (Dusk.mark x).1) using 2
    simp [Dusk.mark]
  unfold untie
  rw [half]
  exact Dusk.tied (Dusk.mark x) (Dusk.mark x) rfl

private theorem films_size (l : Dusk.Film) : size l = 2*l.length+1 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [size_cons,List.length_cons,ih,show size b = 1 from rfl]
    omega

private theorem ties_size (l : List Dusk.Pair) : size (l.map Dusk.tie) ≤ size l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons,size_cons,films_size,Dusk.tie_length,size_prod,Bits.size_word]
    omega

variable {I : Type} (k : I → ℕ) (x : (i : I) → Fin (2^k i) → Record (k i))

/-- Bit cloth in the exact native row and column enumeration. -/
abbrev nativeRows (v : (i : I) → Block 2 (k i) → Record (k i)) :=
  DigitPacking.recordCloth (fun i => line 2 (k i)) (fun i => componentBits (k i)) v

private theorem native_encode (i : I) :
    nativeRows k (fun i a => x i (flatAddress 2 (k i) a)) i = send (filmRows (x i)) := by
  unfold nativeRows DigitPacking.recordCloth cloth stackRun
  simp only [stripe_eq',Dusk.stockera]
  have tab := line_tab_addresses 2 (k i) (fun j => Dusk.tie (Dusk.mark (x i j)))
  simpa only [Function.comp_def,filmRows,Odd.words,List.map_ofFn] using congrArg send tab

/-- A position program's physical cloth interface yields a flat-word task.
The extra term in each budget is the original record volume. -/
theorem route (p : (i : I) → Equiv.Perm (Fin (k i))) (t r : I → ℕ)
    (native : BoundedTask t r
      (fun i => .fork (send (table (p i))) (nativeRows k (fun i a => x i (flatAddress 2 (k i) a)) i))
      (nativeRows k (fun i a => x i (flatAddress 2 (k i) ((permuteNative (p i)).symm a))))) :
    BoundedTask (fun i => t i+Odd.volume (k i)) (fun i => r i+Odd.volume (k i))
      (fun i => send (table (p i),Odd.words (x i)))
      (fun i => send (Odd.words (x i ∘ BoxFin.bitAddress (p i)))) := by
  let y (i : I) := x i ∘ BoxFin.bitAddress (p i)
  have reordered (i : I) : nativeRows k (fun i a => x i (flatAddress 2 (k i) ((permuteNative (p i)).symm a))) i =
      send (filmRows (y i)) := by
    simpa only [flat_native_symm,y,Function.comp_def] using native_encode k y i
  have task : BoundedTask t r (fun i => send (table (p i),filmRows (x i))) (fun i => send (filmRows (y i))) := by
    apply native.conform (fun _ => rfl) (fun _ => rfl) _ reordered
    intro i
    rw [native_encode]
    rfl
  let a i := (table (p i), Odd.words (x i))
  have prep := BoundedTask.of_time (Easy.fst.pair (Easy.snd.compose Dusk.tie_easy.mapping) |>.on a)
  have post := BoundedTask.of_time (easy_untie.mapping.on (fun i => filmRows (y i)))
  have recover (i : I) : (filmRows (y i)).map untie = Odd.words (y i) := by
    simp [filmRows,Odd.words,Function.comp_def]
  simp only [recover] at post
  have run := (prep.compose task).compose post
  apply run.bound 900 900 <;> intro i
  all_goals
    have tv := GatherProgram.table_volume (p i)
    have raw := GatherProgram.row_volume (x i)
    have film : size (filmRows (y i)) ≤ 400*Odd.volume (k i)+1 :=
      (ties_size (Odd.words (y i))).trans (GatherProgram.row_volume (y i))
  · change size (a i)+t i+size (filmRows (y i))+1 ≤ 900*(t i+Odd.volume (k i)+1)
    simp only [a,size_prod]
    omega
  · change max (max (size (a i)+size (a i)) (r i)) (size (filmRows (y i))+size (filmRows (y i)))+1 ≤
        900*(r i+Odd.volume (k i)+1)
    simp only [a,size_prod]
    omega

end
end PhysicalWalsh.PositionCloth

end NearSquareRoot
end Computability
end OAI
