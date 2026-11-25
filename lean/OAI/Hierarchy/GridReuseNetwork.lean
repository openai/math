import OAI.Hierarchy.GridReuseAddress
import OAI.Hierarchy.GridReuseSpliceEval
import OAI.Hierarchy.CatalystSubstitutionPinned
import OAI.ThreeFlat.BitNetwork.OrderedGlue

namespace OAI
/-! # The open trivalent network obtained by splicing each grid line -/

noncomputable section
namespace Hierarchy.GridReuse

open Catalyst GridThrough ThreeFlat CatalystSubstitution
open scoped Classical BigOperators

variable {F : Type*} [Field F] {m p : ℕ}
variable (n : ℕ) (X : Approximation F (m+1) p)

abbrev Copies (m n : ℕ) := (n+1)^(m+1)
abbrev Outer (n : ℕ) (b : Fin (m+1) → ℕ) (p : ℕ) := Port (Copies m n*p) (width n b)

private def openPort (b : Fin (m+1) → ℕ) (p : ℕ) (e : Fin (rails n b)) (s : Bool) :
    Fin (Fintype.card (Outer n b p)) :=
  Fintype.equivFin _ (.inr ((Fintype.equivFin (Wire (width n b))).symm e,s))

private def junctionSource (b : Fin (m+1) → ℕ) (p : ℕ) (e : Fin (rails n b))
    (t : Fin (n+1)) (s : Bool) :
    BitSource (rails n b*n) (Fintype.card (Outer n b p)) :=
  if s then Fin.lastCases (.pin (openPort n b p e true))
    (fun j => .hidden (finProdFinEquiv (e,j))) t
  else Fin.cases (.pin (openPort n b p e false)) (fun j => .hidden (finProdFinEquiv (e,j))) t

def source (c : Fin (Copies m n)) (j : Port p X.width) :
    BitSource (rails n X.width*n) (Fintype.card (Outer n X.width p)) :=
  match j with
  | .inl i => .pin (Fintype.equivFin _ (.inl (finProdFinEquiv (c,i))))
  | .inr (w,s) =>
      let P := program (n:=n) X.width
      let v : Cell (m+1) n := Program.cellOrdinal.symm c
      junctionSource n X.width p (P.pass v w) (v (P.direction (P.pass v w))) s

/-- Each local component has the original rows and private bits. A shared
catalyst edge contributes just its single summed Boolean variable. -/
def splice : Approximation F (m+1) (Copies m n*p) where
  width := width n X.width
  network := BitNetwork.Ordered.glue (fun _ : Fin (Copies m n) => X.network)
    (fun c i => source n X c ((Fintype.equivFin (Port p X.width)).symm i))

omit [Field F] in
theorem splice_sizes :
    (splice n X).network.cells = Copies m n*X.network.cells ∧
    (splice n X).network.internal = rails n X.width*n+Copies m n*X.network.internal := by
  simp [splice,BitNetwork.Ordered.glue]

omit [Field F] in
theorem splice_size : (splice n X).size ≤ Copies m n*X.size := by
  have pass : rails n X.width*(n+1) = Copies m n * ∑ j, X.width j := by
    rw [rails_eq]
    dsimp [Copies]; rw [pow_succ]; ring
  have counts := splice_sizes n X
  unfold Approximation.size
  rw [counts.1,counts.2]
  change _ + Fintype.card (Port (Copies m n*p) (width n X.width)) ≤ _
  simp only [Port,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  change _ + (_ + rails n X.width * 2) ≤ _ * (_ + _ + (p + Fintype.card (Wire X.width)*2))
  rw [wire_card X.width]
  nlinarith only [pass, Nat.zero_le (rails n X.width*n)]

theorem port_count {k : ℕ} (p : ℕ) (b : Fin k → ℕ) :
    Fintype.card (Port p b) = p + (∑ j, b j)*2 := by
  rw [Fintype.card_sum,Fintype.card_fin,Fintype.card_prod,Fintype.card_bool,wire_card]

omit [Field F] in
theorem endpoints_le_size {k : ℕ} (A : Approximation F k p) :
    2*(∑ j, A.width j) ≤ A.size := by
  have size := port_count p A.width
  change _ ≤ A.network.cells+A.network.internal+Fintype.card (Port p A.width)
  omega

omit [Field F] in
/-- The two open endpoints per retained line contribute the old catalyst-bit
density divided by the side length. All public data bits remain independent. -/
theorem splice_open :
    Fintype.card (Port (Copies m n*p) (splice n X).width) =
      Copies m n*p + 2*rails n X.width ∧
    (n+1)*(2*rails n X.width) ≤ Copies m n*X.size := by
  have total := endpoints_le_size X
  constructor
  · change Fintype.card (Fin (Copies m n*p) ⊕ (Wire (width n X.width) × Bool)) = _
    simp [rails,Nat.mul_comm]
  · calc
      _ = Copies m n * (2 * ∑ j, X.width j) := by rw [rails_eq]; simp [Copies,pow_succ]; ring
      _ ≤ Copies m n * X.size := Nat.mul_le_mul_left _ total

def localPin (d : Fin (Copies m n*p) → Bool) (c : Fin (Copies m n)) (i : Fin p) : Bool :=
  d (finProdFinEquiv (c,i))

def external (b : Fin (m+1) → ℕ) (ends : Wire (width n b) × Bool → Bool) :
    GridDiagonal.Pins (Fin (rails n b)) := fun v => ends ((Fintype.equivFin _).symm v.1,v.2)

private theorem junction_read (b : Fin (m+1) → ℕ) (d : Fin (Copies m n*p) → Bool)
    (ends : Wire (width n b) × Bool → Bool) (q : Fin (rails n b*n) → Bool)
    (e : Fin (rails n b)) (t : Fin (n+1)) (s : Bool) :
    (junctionSource n b p e t s).read q (Sum.elim d ends ∘ (Fintype.equivFin _).symm) =
      junction (external n b ends) (q ∘ finProdFinEquiv) e t s := by
  cases s
  · induction t using Fin.cases <;> simp [junctionSource,junction,openPort,external,BitSource.read]
  · induction t using Fin.lastCases <;> simp [junctionSource,junction,openPort,external,BitSource.read]

set_option maxHeartbeats 1000000 in
/-- The coefficient of the actual ordered row list is the mixed contraction in
the lens argument, with its own original public word supplied at every cell. -/
theorem splice_coeff (d : Fin (Copies m n*p) → Bool) (ends : Wire (width n X.width) × Bool → Bool) :
    (splice n X).coeff (Sum.elim d ends) =
      (program (n:=n) X.width).wiring.mixedEval (fun c => (pinWord X (localPin n d c)).coeff)
        (external n X.width ends) := by
  let P := program (n:=n) X.width
  rw [P.mixedEval_splice (fun _ => rfl) (occupies X.width)]
  let rows := fun _ : Fin (Copies m n) => X.network
  let feed := fun c i => source n X c ((Fintype.equivFin (Port p X.width)).symm i)
  let pins : Fin (Fintype.card (Outer n X.width p)) → Bool :=
    Sum.elim d ends ∘ (Fintype.equivFin (Outer n X.width p)).symm
  change (BitNetwork.Ordered.glue rows feed).eval pins = _
  refine (BitNetwork.Ordered.glue_eval rows feed pins).trans ?_
  let eqv := Equiv.arrowCongr (finProdFinEquiv (m:=rails n X.width) (n:=n)).symm (Equiv.refl Bool)
  let lhs (q : Fin (rails n X.width*n) → Bool) :=
    ∏ c : Fin (Copies m n), (rows c).eval (fun j => (feed c j).read q pins)
  let rhs (q : Fin (rails n X.width) × Fin n → Bool) :=
    ∏ c : Fin (Copies m n), (pinWord X (localPin n d c)).coeff (P.spliceBits (external n X.width ends) q c)
  have perSetting (q : Fin (rails n X.width*n) → Bool) : lhs q = rhs (eqv q) := by
    dsimp only [lhs,rhs,rows]
    apply Finset.prod_congr rfl
    intro c _
    rw [pinWord_coeff]
    change X.network.eval _ = X.network.eval _
    apply congrArg X.network.eval
    funext z
    dsimp only [feed,pins]
    cases h : (Fintype.equivFin (Port p X.width)).symm z with
    | inl i => simp [source,BitSource.read,localPin]
    | inr v => rcases v with ⟨w,s⟩; exact junction_read n X.width d ends q _ _ s
  calc
    _ = ∑ q, lhs q := Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
      (fun _ _ => Finset.prod_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl))
    _ = ∑ q, rhs q := Fintype.sum_equiv eqv lhs rhs perSetting
    _ = _ := Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
      (fun _ _ => Finset.prod_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) (fun _ _ => rfl))


end Hierarchy.GridReuse

end
end OAI
