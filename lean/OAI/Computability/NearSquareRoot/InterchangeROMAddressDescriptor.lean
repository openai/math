import OAI.Computability.NearSquareRoot.InterchangeROMAddressBank
import OAI.Computability.NearSquareRoot.InterchangeROMAddressMirrorHeader
import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineClass

/-! # Compiling a complete affine routing header

A literal specifies two field positions, the forward and backward affine
rows and the catalog of carry pairs. From this literal and the current layout
header one polynomial-time program makes all source/destination comparison
descriptors in physical order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Carry
  IntegerMultiplication.Bits IntegerMultiplication.Strip AffineAddress
namespace Affine

abbrev Rows := InterchangeAffineMask.Row Word × InterchangeAffineMask.Row Word
abbrev Class := InterchangeAffineMask.Class Word
abbrev Static := Rows × List Class
abbrev Template := (Location × Location) × Static
abbrev Face := InterchangeAffineMask.Header Word × Shape3 × Shape3
abbrev Stem := (Word × Rows) × Shape3 × Shape3

def comparisons (p : Stem × Class) : Face × Face :=
  let split := p.1.1
  (((split,p.2),p.1.2),(((split.1,split.2.2,split.2.1),p.2.2,p.2.1),p.1.2))

private theorem comparisons_poly : Poly comparisons := by
  unfold comparisons
  fun_prop

def build (power : Tally × Tally → Word) (p : Template × Header) : List (Face × Face) :=
  let static := p.1.2
  let z := power (p.1.1.1.2.1,p.2.1)
  let left := projection (p.1.1.1,p.2)
  let right := projection (p.1.1.2,p.2)
  static.2.map fun key => comparisons (((z,static.1),left,right),key)

theorem build_poly {power : Tally × Tally → Word} (hp : Poly power) : Poly (build power) := by
  let pre (p : Template × Header) : Stem × List Class :=
    (((power (p.1.1.1.2.1,p.2.1),p.1.2.1),projection (p.1.1.1,p.2),projection (p.1.1.2,p.2)),p.1.2.2)
  have h : Poly pre := by
    unfold pre
    apply Poly.pair _ (by fun_prop)
    apply Poly.pair
    · apply Poly.pair _ (by fun_prop)
      exact (show Poly (fun p : Template × Header => (p.1.1.1.2.1,p.2.1)) from by fun_prop).compose hp
    · apply Poly.pair
      · exact (show Poly (fun p : Template × Header => (p.1.1.1,p.2)) from by fun_prop).compose projection_poly
      · exact (show Poly (fun p : Template × Header => (p.1.1.2,p.2)) from by fun_prop).compose projection_poly
  exact h.compose (Poly.push default default comparisons_poly)

abbrev tag (z : Comparison) := send z.desc

/-- The logical comparisons identify the physical layout and carry masks.
The serialized configuration passed to the command is defined by 'build'
using only the literal and the live header. -/
structure Input (power : Tally × Tally → Word) extends BankInput Comparison Comparison.result where
  static : Template
  layout : Header
  describes : send (build power (static,layout)) = Task.forest (pairDesc tag) toBankInput.configs

def input {power} (x : Input power) : Tree :=
  .fork (send x.layout) (send (x.rows.source.map Prod.snd))

/-- Only the single template tree is installed by generated code. -/
def compile (core : Cmd) (static : Template) : Cmd :=
  (Task.prepare 0 (send static)).join ((pack 0).join core)

private theorem shuffle :
    Easy (fun p : Template × (Header × List Tree) => ((p.1,p.2.1),p.2.2)) := by fun_prop

/-- There are fixed commands and exponents for every affine mask catalog.
All three term sizes are explicit: the literal setup, the descriptor header
generation, and the sum of independent comparison and stable routing prices. -/
theorem controller {power : Tally × Tally → Word} (hp : Poly power) :
    ∃ (core : Cmd) (K d e : ℕ), ∀ (x : Input power) env deck,
      Fits env (compile core x.static) (pile 0 (input x) deck) (pile 0 x.rows.answer deck)
        (K * ((size x.static + (input x).count + 1) +
          (size (x.static,x.layout)+1)^e +
          BankInput.total tag (Comparison.budget d) x.toBankInput + 1)) := by
  obtain ⟨d,each⟩ := Comparison.program
  obtain ⟨u,⟨e,C,pc⟩,headers⟩ := build_poly hp
  let start (x : Input power) := (x.static,(x.layout,x.rows.source.map Prod.snd))
  have sw := shuffle.on start
  have head := (headers.on (fun x : Input power => (x.static,x.layout))).left
    (fun x => send (x.rows.source.map Prod.snd))
  have arranged := (sw.compose head).conform (fun _ => rfl) (fun _ => rfl)
    (fun x => congrArg (fun t => Tree.fork t (send (x.rows.source.map Prod.snd))) x.describes)
  have move := (BankInput.program tag (Comparison.budget d) each).on
    (@Input.toBankInput power)
  obtain ⟨core,D,run⟩ := arranged.compose move
  refine ⟨core,5 + D*(C+1) + 6,d,e,?_⟩
  intro x env deck
  have push := Task.fits_prepare 0 (send x.static) env (pile 0 (input x) deck)
  have pair := fits_pack (send x.static) (input x) deck 0 env
  have all := push.join (pair.join (run x env deck))
  refine all.mono ?_
  have h := pc (x.static,x.layout)
  let a := size x.static + (input x).count + 1
  let b := (size (x.static,x.layout)+1)^e
  let r := BankInput.total tag (Comparison.budget d) x.toBankInput
  have hs : size (start x) = a := rfl
  have hu : u (x.static,x.layout) ≤ C*b := h
  change 5*size x.static + (1+D*((size (start x)+u (x.static,x.layout))+r+1)+2)+2 ≤
    (5+D*(C+1)+6)*(a+b+r+1)
  rw [hs]
  have lo : size x.static ≤ a := by dsimp only [a]; omega
  have bound : a + u (x.static,x.layout) +r+1 ≤ (C+1)*(a+b+r+1) := by
    rw [Nat.add_mul,Nat.one_mul]
    have q := Nat.mul_le_mul_left C (show b ≤ a+b+r+1 by omega)
    omega
  have endBound := Nat.mul_le_mul_left D bound
  rw [Nat.add_mul,Nat.add_mul,Nat.mul_assoc]
  omega

end Affine
end InterchangeROMAddress

end NearSquareRoot
end Computability
end OAI
