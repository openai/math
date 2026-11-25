import OAI.Computability.NearSquareRoot.FixedCandidateCRTSweep
import OAI.Computability.NearSquareRoot.PhysicalWalshPositionCloth
import OAI.Computability.NearSquareRoot.BoundedProductRight

/-! # Charged conversion of arbitrary CRT record arrays to and from physical bit rows -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTStream
open IntegerMultiplication Code FixedPoint DigitPacking Space Adic Packed Loom Strip Controlled
open PhysicalWalsh.PositionCloth

noncomputable section

variable {I H : Type} [Codec H] (n : I → ℕ)

/-- Each original tape record is a row, enumerated in natural address order. -/
def clothRows (x : (i : I) → Array (n i)) :=
  nativeRows (fun i => addressBits (n i)) (fun i a => x i (flatAddress 2 _ a))

theorem clothRows_encode (x : (i : I) → Array (n i)) (i : I) :
    clothRows n x i = send ((records (x i)).map Dusk.tie) := by
  unfold clothRows nativeRows recordCloth cloth stackRun
  simp only [stripe_eq',Dusk.stockera]
  have tab := line_tab_addresses 2 (addressBits (n i)) (fun j => Dusk.tie (Dusk.mark (x i j)))
  change _ = send ((List.ofFn (fun j : Fin (2^addressBits (n i)) => Dusk.mark (x i j))).map Dusk.tie)
  simpa only [Function.comp_def,List.map_ofFn] using congrArg send tab

private theorem ties_le (l : List Dusk.Pair) : size (l.map Dusk.tie) ≤ size l := by
  have hf (q : Dusk.Film) : size q = 2*q.length+1 := by
    induction q with
    | nil => rfl
    | cons a as ih => simp only [size_cons,List.length_cons,ih,show size a = 1 from rfl]; omega
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,size_cons,hf,Dusk.tie_length,size_prod,Bits.size_word]
    omega

private theorem easyAt {X Y : Type} [Codec X] [Codec Y] (f : X → Y) (ef : Easy f)
    (x : I → X) (C : ℕ) (h : ∀ i, size (x i) ≤ C*(n i+1)) :
    BoundedTask n n (send ∘ x) (send ∘ f ∘ x) := by
  exact (BoundedTask.of_time (ef.on x)).bound (C+1) (2*C+1)
    (fun i => by have := h i; rw [Nat.add_mul]; omega)
    (fun i => by have := h i; change size (x i)+size (x i)+1 ≤ _; rw [Nat.add_mul,Nat.mul_assoc]; omega)

private def packFilm (p : H × Tally × List Dusk.Pair) := (p.2.1,p.1,p.2.2.map Dusk.tie)

private theorem packFilm_easy : Easy (packFilm (H := H)) :=
  Easy.snd.fstCompose.pair (Easy.fst.pair (Easy.snd.sndCompose.compose Dusk.tie_easy.mapping))

private def unpackFilm (p : Tally × List Dusk.Film) := (p.1,p.2.map untie)

private theorem unpackFilm_easy : Easy unpackFilm := Easy.fst.pair (Easy.snd.compose easy_untie.mapping)

/-- Move the ruler outside the native call and serialise each fixed-width record once. -/
theorem beginRows (hn : ∀ i, 2 ≤ n i) (header : I → H) (K : ℕ)
    (keySize : ∀ i, size (header i) ≤ K*(n i+1)) (x : (i : I) → Array (n i)) :
    BoundedTask n n (fun i => .fork (send (header i)) (framed (x i)))
      (fun i => .fork (send (tally (n i))) (.fork (send (header i)) (clothRows n x i))) := by
  let inp i := (header i,tally (n i),records (x i))
  have run := easyAt n packFilm packFilm_easy inp (K+75001) (fun i => by
    have h := keySize i
    have g : size (tally (n i),records (x i)) ≤ 75000*(n i+1) := framed_size (hn i) _
    change size (header i)+size (tally (n i),records (x i))+1 ≤ _
    rw [Nat.add_mul]; omega)
  exact run.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun i => by rw [clothRows_encode]; rfl)

/-- Split each row back into its signed component words, retaining the original ruler. -/
theorem endRows (hn : ∀ i, 2 ≤ n i) (y : (i : I) → Array (n i)) :
    BoundedTask n n (fun i => .fork (send (tally (n i))) (clothRows n y i))
      (fun i => framed (y i)) := by
  let films i := (tally (n i),(records (y i)).map Dusk.tie)
  have run := easyAt n unpackFilm unpackFilm_easy films 75000 (fun i => by
    have h : size (tally (n i),records (y i)) ≤ 75000*(n i+1) := framed_size (hn i) _
    have hh := ties_le (records (y i))
    simp only [films,size_prod] at h ⊢
    omega)
  apply run.conform (fun _ => rfl) (fun _ => rfl)
  · intro i; rw [clothRows_encode]; rfl
  · intro i
    change send (tally (n i),((records (y i)).map Dusk.tie).map untie) = send (tally (n i),records (y i))
    simp [records,Function.comp_def]

/-- Keep the original operand length outside the native stage. Both conversions cost
linear time in the physical packet, independent of the stage's time allowance. -/
theorem fromNative (hn : ∀ i, 2 ≤ n i) (header : I → H) (K : ℕ)
    (keySize : ∀ i, size (header i) ≤ K*(n i+1))
    (x y : (i : I) → Array (n i)) (t : I → ℕ)
    (native : BoundedTask t n (fun i => .fork (send (header i)) (clothRows n x i)) (clothRows n y)) :
    BoundedTask (fun i => t i+n i) n (fun i => .fork (send (header i)) (framed (x i)))
      (fun i => framed (y i)) := by
  let clock i := t i+n i
  have middle := (native.right (fun i => send (tally (n i)))).bound (time' := clock) (space' := n) 3 4
    (fun i => by change size (tally (n i)) + t i + 1 ≤ 3*(t i+n i+1); simp only [size_tally,tally_length]; omega)
    (fun i => by change n i + size (tally (n i)) + 1 ≤ _; simp only [size_tally,tally_length]; omega)
  have grow (i : I) : n i ≤ clock i := Nat.le_add_left ..
  exact sequence ((beginRows n hn header K keySize x).mono grow (fun _ => le_rfl))
    (sequence middle ((endRows n hn y).mono grow (fun _ => le_rfl)))

end
end FixedCandidate.CRTStream

end NearSquareRoot
end Computability
end OAI
