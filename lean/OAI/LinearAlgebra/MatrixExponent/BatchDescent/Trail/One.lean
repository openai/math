import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Hop

/-!
# Receiving origin labels from neighboring hosts

Relay one dictionary and one short mark per span. The upper half
of the hop bank contains the record at the static parent itself.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
open Assembly Coloring
open scoped Classical

variable {F : Type} {S U : Scheme F} {h d e : ℕ}

abbrev source (S : Scheme F) (h d e : ℕ) := S.format.pair (format S h d e)
abbrev bank (S : Scheme F) (h d e : ℕ) := Fmt.bank S.m S.d (rowFormat S h d e)
private abbrev mail (S : Scheme F) (h d e : ℕ) := receipts S S S.d h d e

private def rebank (x : (source S h d e).obj) : (bank S h d e).obj :=
  fun i => ((x.1 i).1, x.2.row i)

private def dispatch (parent : B U.m → B S.m) (x : (bank S h d e).obj × (mail S h d e).obj) :
    (receipts S U (S.d + 1) h d e).obj :=
  fun i j => if hj : j.val < 2 ^ S.d then x.2 (parent i) ⟨j.val, hj⟩ else (x.1 (parent i)).2

def gatherBound (S U : Scheme F) (h d e v n : ℕ) :=
  gatherCost S.m S.d v n + 64 * ((source S h d e).width + (bank S h d e).width +
    (mail S h d e).width + (receipts S U (S.d + 1) h d e).width)

variable [Field F] {I : Type*} {u v n : ℕ} {L : Set (Table F)}

private theorem rebank_net :
    Circuit F (source S h d e) (bank S h d e) rebank
      ((source S h d e).width + 2 * (bank S h d e).width) := by
  let read : (bank S h d e).pins → (source S h d e).pins
    | (i, .inl p) => .inl (i, .inl p)
    | (i, .inr (.inl (j, p))) => .inr (.inl (locate i j, p))
    | (i, .inr (.inr p)) => .inr (.inr (i, p))
  apply Circuit.project read
  rintro x ⟨i, p | ⟨j, p⟩ | p⟩ <;> rfl

private theorem dispatch_net (parent : B U.m → B S.m) :
    Circuit F (.pair (bank S h d e) (mail S h d e)) (receipts S U (S.d + 1) h d e) (dispatch parent)
      ((Format.pair (bank S h d e) (mail S h d e)).width + 2 * (receipts S U (S.d + 1) h d e).width) := by
  let read : (receipts S U (S.d + 1) h d e).pins → (Format.pair (bank S h d e) (mail S h d e)).pins
    | (i, j, p) => if hj : j.val < 2 ^ S.d then .inr (parent i, ⟨j.val, hj⟩, p)
        else .inl (parent i, .inr p)
  apply Circuit.project read
  rintro x ⟨i, j, p⟩
  change dispatch parent x i j p = _
  unfold dispatch read
  dsimp only
  split <;> rfl

theorem gather (hu : 3 ≤ u) (ht : Access F u L (S.m + S.d) v n) (hv : (rowFormat S h d e).width ≤ v)
    (r : I → S.format.obj) (a : I → Record S h d e) (M : I → Move S U (S.d + 1))
    (parent : B U.m → B S.m)
    (hr : ∀ i, Fmt.Reciprocal (.vec S.h (.addr S.ℓ)) (r i))
    (hn : ∀ i, (M i).nav = subroundNav (U := U) parent (r i)) :
    Computes F u L (source S h d e) (receipts S U (S.d + 1) h d e) (fun i => (r i, a i))
      (fun i => (M i).received (a i)) (fun _ => 1) (gatherBound S U h d e v n) := by
  let Y (i : I) := rebank (S := S) (r i, a i)
  let A := rowFormat S h d e
  have start := Computes.of_map (L := L) (x := fun i => (r i, a i)) (y := Y)
    (Map.circuit hu (rebank_net (S := S))) (fun _ => rfl)
  have keep := Computes.of_map (L := L) (x := Y) (y := Y)
    (Map.circuit hu (Circuit.id F (bank S h d e))) (fun _ => rfl)
  have send := gather_neighbors A hu ht hv Y hr
  have post := Computes.of_map (L := L) (x := fun i => (Y i, Fmt.gather A (Y i)))
    (y := fun i => (M i).received (a i)) (Map.circuit hu (dispatch_net (U := U) parent)) (by
      intro i
      funext j k
      unfold dispatch Move.received
      rw [hn]
      unfold subroundNav
      split <;> rfl)
  have all := (start.comp (keep.pair hu send)).comp post
  simp only [one_mul] at all
  refine all.mono ?_
  simp only [gatherBound, Format.width_pair]
  omega

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

/-!
# Carrying exterior data through a weighted step

The ordinary transition produces the return pointers. In parallel,
the previous origins are gathered and then compacted using those pointers.
Only the ordinary transition supplies a weight.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
open Assembly Coloring

variable {F : Type} {S U : Scheme F} {k h d e : ℕ}

def carryCost (S U : Scheme F) (k h d d' e : ℕ) (A T : Format) :=
  20 * A.width + 16 * (T.width + (feed S U k h d e).width) + 4 * cost S U k h d d' e

variable [Field F] {I : Type*} {u m n : ℕ} {L : Set (Table F)}
  {A T : Format} {x : I → A.obj} {y : I → T.obj} {w : I → F}

theorem carry (hu : 3 ≤ u) (d' : ℕ) (M : I → Move S U k) (a : I → Record S h d e)
    (commands : Computes F u L A (.pair T (controls S U k))
      x (fun i => (y i, (M i).commands)) w m)
    (mail : Computes F u L A (receipts S U k h d e)
      x (fun i => (M i).received (a i)) (fun _ => 1) n) :
    Computes F u L A (.pair T (format U h d' e))
      x (fun i => (y i, (M i).update d' (a i))) w (m + n + carryCost S U k h d d' e A T) := by
  let C := controls S U k
  let R := receipts S U k h d e
  let X := (T.pair C).pair R
  let Y := T.pair (R.pair C)
  have order : Circuit F X Y (fun z => (z.1.1, z.2, z.1.2)) (X.width + 2 * Y.width) := by
    apply Circuit.project (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)))
    rintro _ (i|i|i) <;> rfl
  obtain ⟨f, hf, he⟩ := execute_net F S U k h d d' e
  have post := Map.circuit (L := L) hu (order.comp ((Circuit.id F T).par hf))
  have run := (commands.pair hu mail).comp (Computes.of_map post
    (y := fun i => (y i, (M i).update d' (a i))) (by intro i; exact congrArg (Prod.mk (y i)) (he (M i) (a i))))
  simp only [mul_one] at run
  refine run.mono ?_
  simp only [carryCost, feed, X, Y, C, R, Format.width_pair]
  omega

theorem propagate {v s : ℕ} (hu : 3 ≤ u) (d' : ℕ)
    (ht : Access F u L (S.m + S.d) v s) (hv : (rowFormat S h d e).width ≤ v)
    (r : I → S.format.obj) (a : I → Record S h d e) (M : I → Move S U (S.d + 1))
    (parent : B U.m → B S.m)
    (hr : ∀ i, Fmt.Reciprocal (.vec S.h (.addr S.ℓ)) (r i))
    (hn : ∀ i, (M i).nav = subroundNav (U := U) parent (r i))
    (commands : Computes F u L A (.pair T (controls S U (S.d + 1)))
      x (fun i => (y i, (M i).commands)) w m)
    (read : Computes F u L A (source S h d e) x (fun i => (r i, a i)) (fun _ => 1) n) :
    Computes F u L A (.pair T (format U h d' e))
      x (fun i => (y i, (M i).update d' (a i))) w
      (m + n + gatherBound S U h d e v s + carryCost S U (S.d + 1) h d d' e A T) := by
  have mail := read.comp (gather hu ht hv r a M parent hr hn)
  simp only [one_mul] at mail
  simpa only [add_assoc] using carry hu d' M a commands mail

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

/-! # A reset gathers origin marks only at the static parent -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
open Assembly Coloring
variable {F : Type} [Field F] {S U : Scheme F} {I : Type*} {h d d' e u m : ℕ}
  {L : Set (Table F)} {A T : Format} {x : I → A.obj} {y : I → T.obj} {w : I → F}

theorem one (hu : 3 ≤ u) (M : I → Move S U 0) (a : I → Record S h d e)
    (parent : B U.m → B S.m) (hp : ∀ i j b, (M i).nav j b = parent j)
    (commands : Computes F u L A (.pair T (controls S U 0))
      x (fun i => (y i, (M i).commands)) w m) :
    Computes F u L (.pair A (format S h d e)) (.pair T (format U h d' e))
      (fun i => (x i, a i)) (fun i => (y i, (M i).update d' (a i))) w
      (m + 2 * carryCost S U 0 h d d' e (.pair A (format S h d e)) T) := by
  let D := A.pair (format S h d e)
  let R := receipts S U 0 h d e
  let old : I → D.obj := fun i => (x i, a i)
  have read : Circuit F D A Prod.fst (D.width + 2 * A.width) := Circuit.project Sum.inl fun _ _ => rfl
  let f (s : D.obj) : R.obj := fun j _ => s.2.row (parent j)
  let pins : R.pins → D.pins
    | (j, _, .inl (i, b)) => .inr (.inl (locate (parent j) i, b))
    | (j, _, .inr p) => .inr (.inr (parent j, p))
  have send : Circuit F D R f (D.width + 2 * R.width) := by
    apply Circuit.project pins
    rintro b ⟨j, k, i|p⟩ <;> rfl
  have step := (Computes.of_map (x := old) (y := x) (Map.circuit (L := L) hu read)
    (fun _ => rfl)).comp commands
  have mail := Computes.of_map (x := old) (y := fun i => (M i).received (a i))
    (Map.circuit (L := L) hu send) (by
      intro i; funext j k; simp only [f, old, Move.received, hp])
  simp only [one_mul] at step
  refine (carry hu d' M a step mail).mono ?_
  simp only [carryCost, feed, D, R, Format.width_pair]
  omega

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end
