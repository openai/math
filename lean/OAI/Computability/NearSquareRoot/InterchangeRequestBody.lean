import OAI.Computability.NearSquareRoot.InterchangeFrameBody
import OAI.Computability.NearSquareRoot.InterchangeRequestHeader

/-! # A recursion step on the literal interchange request -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress.Request

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Adic IntegerMultiplication.Loom NearSquareRoot.InterchangeFrame

variable {I X J : Type} {b n : ℕ} [NeZero b]

def widthView (P G B : Dims.Tape) {u v : ℕ} (eq : u = v) :
    Adopt (stock b P G B u) (stock b P G B v) := by
  subst v
  exact Adopt.same _

omit [NeZero b] in
theorem widthView_swap (P G B : Dims.Tape) {u v : ℕ} (eq : u = v)
    (z : SpanKey P G B (Block b u)) :
    (widthView P G B eq).cast (swapper _ _ _ z) = swapper _ _ _ ((widthView P G B eq).cast z) := by
  subst v
  rfl

/-- On each internal request compute the quotient and remainder from the
encoded header, expose the smaller fields, run the center program, and scan
the two short endpoints. The child list and the work certificate refer to
the actual issue and reply, retaining the center program's full accounting. -/
theorem framed_step (hb : 2 ≤ b) (hn : 0 < n) (ord : J ≃ Fin n) (xs : I → Request b)
    (admissible : ∀ i, Admissible (xs i)) (internal : ∀ i, n < (xs i).width)
    (oracle : Job X) (good : I → Tree → Prop) (account : I → List X → Prop)
    (valid : ∀ i a, good i ((xs i).contents a))
    (hv : Manifest _ (fun i => (xs i).recordWidth) (fun i => (xs i).contents))
    (body : InterchangeFrame.Program oracle (regime xs) (fun i => (xs i).recordWidth) account good
      (fun i => arrays ord (line b (lanes n (xs i).width)) (pre b 1 (xs i).before)
        (gap b 1 (tail n (xs i).width) (xs i).between) (post b (tail n (xs i).width) (xs i).after_))
      (fun _ => swapper _ _ _)) :
    ∃ uses : I → List X, (∀ i, account i (uses i)) ∧
      Quest oracle (regime xs) (fun i => (xs i).rows.count) (fun i => (xs i).recordWidth)
        uses ((job b).issue ∘ xs) ((job b).reply ∘ xs) := by
  obtain ⟨hp,hg,hs⟩ := shapes_told xs admissible
  have whole := assemble ord _ _ _ _ _ _ hb n (fun _ => hn) (fun _ => (tail_lt _ hn).le)
    (Regime.fixed (tally 1)) (lane_has xs n) (tail_has xs n) hp hg hs body
  let eq i := width_eq (by have := internal i; omega : 0 < (xs i).width) n
  let view i := widthView (b:=b) (xs i).before (xs i).between (xs i).after_ (eq i)
  have parent := Program.align (s:=fun i => (xs i).rows) view (fun i => widthView_swap _ _ _ (eq i)) whole
  exact parent (fun i => (xs i).contents) hv valid

end InterchangeAddress.Request

end NearSquareRoot
end Computability
end OAI
