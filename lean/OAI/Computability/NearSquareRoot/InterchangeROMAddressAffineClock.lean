import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineEstimate
import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineProgram

/-! # The affine controller's full-stream bound

The catalog length is a template constant. The only live-size term multiplied
by the volume of addresses is polynomial in the compact layout header and the
literal template.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMAddress.Affine

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom Space AffineAddress

abbrev Active := Input InterchangeAffineMask.modulus
abbrev recordVolume (x : Active) :=
  size (x.rows.source.map Prod.snd) + size (x.rows.target.map Prod.snd) + 1
abbrev shapeVolume (t : Template × Header) := size (build InterchangeAffineMask.modulus t)

def overhead (d e : ℕ) (t : Template × Header) :=
  (size t+1) + (size t+1)^e + shapeVolume t + 2*localPrice d (shapeVolume t) + 1

theorem overhead_polynomial (d e : ℕ) : Dom size (overhead d e) := by
  have h : Dom size shapeVolume := (build_poly InterchangeAffineMask.modulus_poly).length
  have a := h.add (Dom.const size 8)
  have b := ((Dom.const size 40).mul a).add (((Dom.const size 8).mul a).pow d)
  have one := Dom.const (size (X:=Template × Header)) 1
  have base := (Dom.base (size (X:=Template × Header))).add one
  exact ((((base.add (base.pow e)).add h).add ((Dom.const size 2).mul b)).add one)

abbrev work (C j N : ℕ) (x : Active) :=
  (x.rows.colors.length+1) * (recordVolume x + (N+1)*(C*(size (x.static,x.layout)+1)^j))

def Priced (N d : ℕ) (x : Active) : Prop :=
  let H := shapeVolume (x.static,x.layout)
  BankInput.total tag (Comparison.budget d) x.toBankInput ≤
    (x.rows.colors.length+1) * (H + 2*((N+1)*localPrice d H) +
      size (x.rows.source.map Prod.snd) + size (x.rows.target.map Prod.snd) + 1)

theorem cap_le (K d e : ℕ) :
    ∃ C j, ∀ (N : ℕ) (x : Active), Priced N d x →
      (input x).count + time K d e x ≤ (5*K+3)*work C j N x := by
  obtain ⟨j,C,upper⟩ := overhead_polynomial d e
  refine ⟨C,j,?_⟩
  intro N x priced
  let t := (x.static,x.layout)
  let F := overhead d e t
  let H := shapeVolume t
  let price := localPrice d H
  let V := recordVolume x
  let W := work C j N x
  have fcap : F ≤ C*(size t+1)^j := upper t
  have nf : (N+1)*F ≤ (N+1)*(C*(size t+1)^j) := Nat.mul_le_mul_left _ fcap
  have b1 : V + (N+1)*F ≤ W := by
    change _ ≤ (x.rows.colors.length+1)*(V+(N+1)*(C*(size t+1)^j))
    exact (Nat.add_le_add_left nf _).trans (Nat.le_mul_of_pos_left _ (by omega))
  have hF : H+2*price ≤ F := by dsimp only [F,overhead,H,price]; omega
  have aF : size t+1 ≤ F := by dsimp only [F,overhead]; omega
  have pF : (size t+1)^e ≤ F := by dsimp only [F,overhead]; omega
  have ceil_price : H + 2*((N+1)*price) ≤ (N+1)*F := by
    have := Nat.mul_le_mul_left (N+1) hF
    rw [Nat.mul_add,Nat.mul_left_comm (N+1) 2] at this
    have hh := Nat.le_mul_of_pos_left H (show 0<N+1 by omega)
    omega
  have fW : F ≤ W := by have := Nat.le_mul_of_pos_left F (show 0<N+1 by omega); omega
  have bank : BankInput.total tag (Comparison.budget d) x.toBankInput ≤ W := by
    apply priced.trans
    apply Nat.mul_le_mul_left
    change H+2*((N+1)*price)+_+_+1 ≤ V+(N+1)*(C*(size t+1)^j)
    dsimp only [V,recordVolume]
    omega
  have si : size x.static + (input x).count + 1 ≤ W := by
    have := Nat.le_mul_of_pos_left F (show 0<N+1 by omega)
    change size x.static + (size x.layout + size (x.rows.source.map Prod.snd) + 1) + 1 ≤ W
    change size x.static + size x.layout + 1 + 1 ≤ F at aF
    dsimp only [V,recordVolume] at b1
    omega
  have priceW : (size (x.static,x.layout)+1)^e ≤ W := pF.trans fW
  have unitW : 1 ≤ W := by omega
  have timeW : time K d e x ≤ K*(5*W) := by
    apply Nat.mul_le_mul_left
    omega
  change _ ≤ (5*K+3)*W
  rw [Nat.add_mul,Nat.mul_comm 5 K,Nat.mul_assoc]
  omega

variable {J : Type} [DecidableEq J] {n b f : ℕ} [NeZero b] (ord : J ≃ Fin n)
  (P G S : Tape) (hp : solid P) (hg : solid G) (hs : solid S) (hb : 2 ≤ b)

theorem width_priced (x : Spot J) (a : Span b) (v : Keys P G S J (Block b f) → Tree) (d : ℕ) :
    Priced (arrays ord (line b f) P G S).count d (width ord P G S hp hg hs hb x a v) := by
  let z := width ord P G S hp hg hs hb x a v
  have native := native_price ord P G S hp hg hs hb x x
    (InterchangeAffineMask.widthRows a.neg a.top.count a.down.count).1
    (InterchangeAffineMask.widthRows a.neg a.top.count a.down.count).2 d z.toBankInput (fun _ _ => rfl)
  have sizes := congrArg Tree.count z.describes
  change Priced _ _ z
  change shapeVolume (z.static,z.layout) = headerCount tag z.toBankInput at sizes
  unfold Priced
  rw [sizes]
  exact native

theorem gather_priced (x y : Spot J) (legal : Lag.early (ranking ord) x y) (a : Pinpoint b)
    (v : Keys P G S J (Block b f) → Tree) (d : ℕ) :
    Priced (arrays ord (line b f) P G S).count d (gather ord P G S hp hg hs hb x y legal a v) := by
  let z := gather ord P G S hp hg hs hb x y legal a v
  have native := native_price ord P G S hp hg hs hb x y (InterchangeAffineMask.pinRows a).1
    (InterchangeAffineMask.pinRows a).2 d z.toBankInput (fun _ _ => rfl)
  have sizes := congrArg Tree.count z.describes
  change Priced _ _ z
  change shapeVolume (z.static,z.layout) = headerCount tag z.toBankInput at sizes
  unfold Priced
  rw [sizes]
  exact native

/-- Uniform bounds on all actual open calls satisfying the native price
certificate, including every single-field and two-field instruction. -/
theorem run_native : ∃ M C j d : ℕ, ∀ N (x : Active), Priced N d x → ∀ env deck base, DeckCap base deck →
    BoundedFits env (compile core x.static) (pile 0 (input x) deck) (pile 0 x.rows.answer deck)
      (M*work C j N x) (base+M*work C j N x) (M*work C j N x) := by
  obtain ⟨K,d,e,run⟩ := compiled
  obtain ⟨C,j,bound⟩ := cap_le K d e
  refine ⟨5*K+3,C,j,d,?_⟩
  intro N x hx env deck base hbase
  have h := bound N x hx
  exact (run x env deck base hbase).mono (by omega) (by omega) (by omega)

end InterchangeROMAddress.Affine

end NearSquareRoot
end Computability
end OAI
