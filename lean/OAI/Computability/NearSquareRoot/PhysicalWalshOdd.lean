import OAI.Computability.NearSquareRoot.FixedCandidateGuard
import OAI.Computability.NearSquareRoot.PhysicalWalshPadding
import OAI.Computability.NearSquareRoot.PrecisionButterflyFrame
import OAI.Computability.NearSquareRoot.PhysicalWalshOddCoordinates

/-! # Conditional normalized butterfly on the terminal selected bit

After truncating the padded spectator rows, the last selected bit is the
low bit of the ordered record stream. The controller reads the parity of
the selected width from its unary tally and forwards the precision ruler to
the normalized butterfly precisely on the odd branch.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Odd

open IntegerMultiplication Code Space FixedPoint Matrix

def words {k : ℕ} (x : Fin (2^k) → Record k) : List Dusk.Pair :=
  (List.ofFn x).map Dusk.mark

def volume (k : ℕ) := 2^k*(k+1)
def time (k : ℕ) := 2^k*GridTask.recordCost k

private def annotate (p : (Tally × Tally) × List Dusk.Pair) :=
  ((Carry.half p.1.2).2,(p.2,p.1.1))

private theorem easy_annotate : Easy annotate := by
  unfold annotate
  fun_prop

private theorem transport {k s : ℕ} (sel : s ≤ k) (x : Fin (2^k) → Record k) :
    size ((tally k,tally s),words x) ≤ 430*volume k ∧ size (words x,tally k) ≤ 430*volume k := by
  have hn := Nat.two_pow_pos k
  have hp := Nat.mul_le_mul_right ((2:ℕ)^k) (show 1 ≤ k+1 by omega)
  have hk := Nat.le_mul_of_pos_left (k+1) hn
  have width : size (words x) = 2^k*(4*(componentBits k+1)+4)+1 := by
    simpa only [words,List.length_ofFn] using Padding.marks_size (w := componentBits k) (List.ofFn x)
  simp only [size_prod,size_tally,tally_length,width,componentBits,volume]
  ring_nf at *
  omega

variable {I : Type} (k s : I → ℕ) (sel : ∀ i, s i ≤ k i)
  (x y : (i : I) → Fin (2^k i) → Record (k i))

include sel in
/-- The dispatch takes the two compact rulers and the flat array as its input.
Both branches return a flat array with the same record type. -/
theorem dispatch
    (equal : ∀ i, Carry.parity (s i) = false → y i = x i)
    (butterfly : BoundedTask (fun z : {i // Carry.parity (s i) = true} => time (k z.val))
      (fun z => volume (k z.val)) (fun z => send (words (x z.val),tally (k z.val)))
      (fun z => send (words (y z.val)))) :
    BoundedTask (time ∘ k) (volume ∘ k) (fun i => send ((tally (k i),tally (s i)),words (x i)))
      (fun i => send (words (y i))) := by
  let src i := (words (x i),tally (k i))
  let inp i := ((tally (k i),tally (s i)),words (x i))
  have Vle i : volume (k i) ≤ time (k i) :=
    Nat.mul_le_mul_left _ (GridTask.width_le_recordCost _)
  have bounds i := transport (sel i) (x i)
  have skip : BoundedTask (fun z : {i // Carry.parity (s i) = false} => time (k z.val))
      (fun z => volume (k z.val)) (fun z => send (src z.val)) (fun z => send (words (y z.val))) := by
    let arg (z : {i // Carry.parity (s i) = false}) := src z.val
    have run := BoundedTask.of_time (Easy.fst.on arg)
    have mapped : ∀ z, (arg z).1 = words (y z.val) := fun z => by rw [equal z.val z.property]
    simp only [mapped] at run
    apply run.bound 440 880 <;> intro z
    · change size (src z.val)+1 ≤ _
      have h : size (src z.val) ≤ 430*time (k z.val) := (bounds z.val).2.trans (Nat.mul_le_mul_left 430 (Vle z.val))
      omega
    · change size (src z.val)+size (src z.val)+1 ≤ _
      have h : size (src z.val) ≤ 430*volume (k z.val) := (bounds z.val).2
      omega
  have go := BoundedTask.control (fun i => Carry.parity (s i)) (src := fun i => send (src i))
    (t := fun i => time (k i)) (s := fun i => volume (k i)) (dst := fun i => send (words (y i))) skip butterfly
  have tag := BoundedTask.of_time (easy_annotate.on inp)
  have parsed i : annotate (inp i) = (Carry.parity (s i),src i) := by simp [annotate,inp,src,Carry.half_v]
  simp only [parsed] at tag
  have chain := tag.compose go
  apply chain.bound 900 900 <;> intro i
  · change size (inp i)+time (k i)+1 ≤ 900*(time (k i)+1)
    have h : size (inp i) ≤ 430*time (k i) := (bounds i).1.trans (Nat.mul_le_mul_left 430 (Vle i))
    omega
  · change max (size (inp i)+size (inp i)) (volume (k i)+size (src i))+1 ≤ 900*(volume (k i)+1)
    have hp : size (inp i) ≤ 430*volume (k i) := (bounds i).1
    have hq : size (src i) ≤ 430*volume (k i) := (bounds i).2
    omega


/-- Return the original records or the normalized adjacent-pair result, as
selected by the low bit of the unary width. -/
def finish {k : ℕ} (s : ℕ) (x : Fin (2^k) → Record k) :=
  if h : 1 ≤ k ∧ s%2 = 1 then output h.1 x else x

include sel in
/-- Physical terminal pass on the original array after discarding the
spectator padding. The command also covers the single-slot array. -/
theorem bounded :
    BoundedTask (time ∘ k) (volume ∘ k) (fun i => send ((tally (k i),tally (s i)),words (x i)))
      (fun i => send (words (finish (s i) (x i)))) := by
  apply dispatch k s sel x
  · intro i h
    have hf : s i % 2 ≠ 1 := of_decide_eq_false h
    simp [finish,hf]
  let Z := {i // Carry.parity (s i) = true}
  have modOne (z : Z) : s z.val % 2 = 1 := of_decide_eq_true z.property
  have hk (z : Z) : 1 ≤ k z.val := by have := sel z.val; have := modOne z; omega
  have dim (z : Z) : 2*2^(k z.val-1) = 2^k z.val := by
    rw [Nat.mul_comm,← pow_succ,show k z.val-1+1=k z.val by have := hk z; omega]
  let m (z : Z) := 2^(k z.val-1)
  have run := ButterflyTask.oddBitArrayBounded (fun z : Z => k z.val) m
    (fun z => x z.val ∘ pack (hk z)) dim
  have M (z : Z) : m z + 1 ≤ 2^k z.val := by
    have d : 2*m z = 2^k z.val := dim z
    have pos : 0 < m z := Nat.two_pow_pos _
    omega
  have run' := run.mono (fun z => Nat.mul_le_mul_right _ (M z)) (fun z => Nat.mul_le_mul_right _ (M z))
  apply run'.conform (fun _ => rfl) (fun _ => rfl)
  · intro z; rw [input_words]; rfl
  · intro z; rw [output_words]; simp [words,finish,hk z,modOne z]

theorem words_range {k : ℕ} (x : ℕ → Record k) :
    words (fun j : Fin (2^k) => x j.val) = (List.range (2^k)).map (Dusk.mark ∘ x) := by
  apply List.ext_getElem
  · simp [words]
  · intro i h₁ h₂
    simp [words]

/-- Use the sweep's natural-address representation on the input side. -/
theorem bounded_range (k s : I → ℕ) (hs : ∀ i, s i ≤ k i) (x : (i : I) → ℕ → Record (k i)) :
    BoundedTask (time ∘ k) (volume ∘ k)
      (fun i => send ((tally (k i),tally (s i)),(List.range (2^k i)).map (Dusk.mark ∘ x i)))
      (fun i => send (words (finish (s i) (fun j => x i j.val)))) := by
  simpa only [words_range] using bounded k s hs (fun i j => x i j.val)

noncomputable section

/-- The terminal exact operation acts isometrically at either parity. -/
def finishIdeal (k s : ℕ) : EuclideanSpace ℂ (Fin (2^k)) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (2^k)) :=
  if h : 1 ≤ k ∧ s%2 = 1 then ideal h.1 else LinearIsometry.id

theorem finishIdeal_at {k s : ℕ} (hs : s ≤ k) (v : ℕ → ℂ) (j : Fin (2^k)) :
    finishIdeal k s (WithLp.toLp 2 (fun i => v i.val)) j =
      FlatWalshNode.activeRow (s%2) 1 v j.val := by
  by_cases h : s%2 = 1
  · have h1 : 1 ≤ k := by omega
    simpa [finishIdeal,h1,h] using ideal_at h1 v j
  · have h0 : s%2 = 0 := by omega
    simp [finishIdeal,h0]

/-- Arithmetic headroom and error for the terminal pass on an array that
already contains rounding error from the even sweep. -/
theorem finish_error55 {k : ℕ} (s : ℕ) (x : Fin (2^k) → Record k)
    (hx : ‖recordArray x‖ ≤ (2:ℝ)^(14*k)) :
    ‖recordArray (finish s x) - finishIdeal k s (recordArray x)‖ ≤ 1/(2:ℝ)^(55*k) := by
  by_cases h : 1 ≤ k ∧ s%2 = 1
  · simpa only [finish,finishIdeal,dite_eq_left h] using output_error55 h.1 x hx
  · simp [finish,finishIdeal,h]

/-- Carry the accumulated error from the even agenda through the final
isometry and identify the exact target as the selected Walsh matrix. -/
theorem complete_error (A W : ℕ) (hA : 1 < A) (hW : 0 < W) {k s : ℕ} (hs : s ≤ k)
    (w : ℕ) (u : ℕ → ℂ) (z : Fin (2^k) → Record k) (guard : ‖recordArray z‖ ≤ (2:ℝ)^(14*k))
    {e : ℝ} (prior : ‖recordArray z - WithLp.toLp 2 (fun j : Fin (2^k) =>
      ((Pieces.schedule A W hW k s w).foldl (fun y p => FlatWalshNode.idealRow A p y) u) j.val)‖ ≤ e) :
    ‖recordArray (finish s z) - WithLp.toLp 2
      (BoxFin.flatWalsh (FlatWalshWindow.bits k s 0 (by omega)) *ᵥ (fun i => u i.val))‖ ≤
        1/(2:ℝ)^(55*k)+e := by
  let v := (Pieces.schedule A W hW k s w).foldl (fun y p => FlatWalshNode.idealRow A p y) u
  let a : EuclideanSpace ℂ (Fin (2^k)) := WithLp.toLp 2 (fun j : Fin (2^k) => v j.val)
  have exactTarget : finishIdeal k s a = WithLp.toLp 2
      (BoxFin.flatWalsh (FlatWalshWindow.bits k s 0 (by omega)) *ᵥ (fun i => u i.val)) := by
    apply PiLp.ext
    intro j
    exact (finishIdeal_at hs v j).trans
      (congrFun (Pieces.ideal_selected A W hA hW k s w hs u) j)
  rw [← exactTarget]
  apply (norm_sub_le_norm_sub_add_norm_sub _ (finishIdeal k s (recordArray z)) _).trans
  apply add_le_add (finish_error55 s z guard)
  rwa [← map_sub,(finishIdeal k s).norm_map]

end
end PhysicalWalsh.Odd

end NearSquareRoot
end Computability
end OAI
