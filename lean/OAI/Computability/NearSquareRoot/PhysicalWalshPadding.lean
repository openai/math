import OAI.Computability.NearSquareRoot.WalshPadding
import OAI.Computability.NearSquareRoot.BoundedProgram
import OAI.Computability.IntegerMultiplication.Code.Dup
import OAI.Computability.IntegerMultiplication.Code.Iter
import OAI.Computability.IntegerMultiplication.Dusk.Nerve

/-! # Appending and discarding the padded spectator records

Padding operates on one flat list of marked complex grid records. The program
uses the first record to determine the word width of a canonical zero. It parks
the original-length ruler during the template and uses it to discard the added
records after the last selected-bit piece.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Padding

open IntegerMultiplication Code Space

variable {I : Type}

def zeroLike (x : Dusk.Pair) : Dusk.Pair :=
  (x.1.map (fun _ => false), x.2.map (fun _ => false))

private theorem easy_zeroLike : Easy zeroLike :=
  (Easy.fst.compose (Easy.const false).mapping).pair (Easy.snd.compose (Easy.const false).mapping)

private theorem trip_zero {w : ℕ} (x : Dusk.day w) :
    (Dusk.trip x).map (fun _ => false) = Dusk.trip (0 : Dusk.day w) := by
  apply Bits.word_inject
  · simp
  · simp only [List.map_const', Dusk.trip_length, Dusk.trips, ZMod.val_zero]
    induction w + 1 with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, Bits.value_cons,ih]

theorem zeroLike_mark {w : ℕ} (x : Dusk.Grain w) : zeroLike (Dusk.mark x) = Dusk.mark (0 : Dusk.Grain w) := by
  exact Prod.ext (trip_zero x.re) (trip_zero x.im)

private def prepare (p : (Tally × Tally) × List Dusk.Pair) :=
  ((p.1.1,zeroLike (p.2.headD ([], []))),(p.1.2,p.2))

private theorem easy_prepare : Easy prepare :=
  ((Easy.fst.compose Easy.fst).pair ((Easy.snd.compose (Iter.leader ([],[]))).compose easy_zeroLike)).pair
    ((Easy.fst.compose Easy.snd).pair Easy.snd)

private def finish (p : List Dusk.Pair × Tally × List Dusk.Pair) :=
  (p.2.1,p.2.2 ++ p.1)

private theorem easy_finish : Easy finish := by unfold finish; fun_prop

theorem marks_size {w : ℕ} (x : List (Dusk.Grain w)) :
    size (x.map Dusk.mark) = x.length * (4*(w+1)+4)+1 := by
  induction x with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, size_cons, Dusk.volume, ih, List.length_cons, Nat.succ_mul]; omega

private theorem size_replicate {Z : Type} [Codec Z] (n : ℕ) (z : Z) :
    size (List.replicate n z) = n * (size z + 1) + 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, size_cons, ih, Nat.succ_mul]; omega

/-- The flat tape after appending `e` additional records on a known grid. -/
def padded {w : ℕ} (e : ℕ) (x : List (Dusk.Grain w)) :=
  x.map Dusk.mark ++ List.replicate e (Dusk.mark (0 : Dusk.Grain w))

/-- Append the exact number of zero records specified by the padding header.
The second tally, for the later truncation, survives unchanged. -/
theorem appendZeros (w e : I → ℕ) (xs : (i : I) → List (Dusk.Grain (w i)))
    (nonempty : ∀ i, xs i ≠ []) :
    let N i := (xs i).length
    let V i := (N i + e i + 1)*(w i + 1)
    BoundedTask V V (fun i => send ((tally (e i),tally (N i)), (xs i).map Dusk.mark))
      (fun i => send (tally (N i), padded (e i) (xs i))) := by
  intro N V
  let z (i : I) := Dusk.mark (0 : Dusk.Grain (w i))
  let word (i : I) := (xs i).map Dusk.mark
  let p (i : I) := ((tally (e i),tally (N i)),word i)
  let q (i : I) := (List.replicate (e i) (z i),tally (N i),word i)
  have prep (i : I) : prepare (p i) = ((tally (e i),z i),(tally (N i),word i)) := by
    simp only [prepare,p,Prod.mk.injEq,true_and,and_true]
    cases E : xs i with
    | nil => exact (nonempty i E).elim
    | cons a l => simp only [word,E,List.map_cons,List.headD_cons,zeroLike_mark,z]
  have gen := (generate.on fun i => (tally (e i),z i)).left (fun i => send (tally (N i),word i))
  simp only [tally_length] at gen
  have setup := easy_prepare.on p
  simp only [prep] at setup
  have mid : Task (fun i => (e i+1)*size (z i)) (fun i => send ((tally (e i),z i),(tally (N i),word i)))
      (fun i => send (q i)) := gen
  have whole := (setup.compose mid).compose (easy_finish.on q)
  have result (i : I) : finish (q i) = (tally (N i), padded (e i) (xs i)) := rfl
  simp only [result] at whole
  apply (BoundedTask.of_time whole).bound 40 60 <;> intro i
  · simp only [p,q,word,z,size_prod,size_tally,tally_length,size_replicate,marks_size,V,N,
      Dusk.mark,Bits.size_word,Dusk.trip_length]
    ring_nf
    omega
  · change size (p i)+(size (p i)+(e i+1)*size (z i)+size (q i))+1 ≤ 60*(V i+1)
    simp only [p,q,word,z,size_prod,size_tally,tally_length,size_replicate,marks_size,V,N,
      Dusk.mark,Bits.size_word,Dusk.trip_length]
    ring_nf
    omega

/-- After the transforms, keep exactly the records of the original array.
The operation works on arbitrary output entries in the padded rows. -/
theorem truncate (w n : I → ℕ) (ys : (i : I) → List (Dusk.Grain (w i)))
    (fits : ∀ i, n i ≤ (ys i).length) :
    let V i := ((ys i).length+1)*(w i+1)
    BoundedTask V V (fun i => send (tally (n i),(ys i).map Dusk.mark))
      (fun i => send (((ys i).take (n i)).map Dusk.mark)) := by
  intro V
  have cut := ((easy_cut (Easy.identity (X := Tally × List Dusk.Pair))).compose Easy.fst).on
    (fun i => (tally (n i),(ys i).map Dusk.mark))
  simp only [cutLists,id_eq,tally_length,← List.map_take] at cut
  apply (BoundedTask.of_time cut).bound 12 24 <;> intro i
  · simp only [size_prod,size_tally,tally_length,marks_size,V]
    have := fits i; ring_nf; omega
  · change size (tally (n i),(ys i).map Dusk.mark)+size (tally (n i),(ys i).map Dusk.mark)+1 ≤ _
    simp only [size_prod,size_tally,tally_length,marks_size,V]
    have := fits i; ring_nf; omega

end PhysicalWalsh.Padding

end NearSquareRoot
end Computability
end OAI
