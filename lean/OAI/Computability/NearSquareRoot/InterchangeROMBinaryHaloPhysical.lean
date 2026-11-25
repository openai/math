import OAI.Computability.NearSquareRoot.InterchangeROMBinaryHaloRun
import OAI.Computability.NearSquareRoot.InterchangeROMBinaryHaloNative

/-! # Physical extension and cropping in compatible mixed-radix tape orders -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BinaryHalo
open IntegerMultiplication Code Strip CommonRegisters Space BoxMaskedRecords

/-- Extend binary-order data to the larger physical order, filling every hole with the supplied record. -/
def extend {I J A : Type} {s : Shape} (d : Addr s s.D ≃ I) (p : Addr s s.E ≃ J)
    (fill : A) (f : I → A) : J → A := padded fill (f ∘ d) ∘ p.symm

/-- Any common property of the filling and occupied records holds throughout the padded bank. -/
theorem extend_prop {I J A : Type} {s : Shape} (d : Addr s s.D ≃ I) (p : Addr s s.E ≃ J)
    {fill : A} {f : I → A} (Q : A → Prop) (hfill : Q fill) (hf : ∀ x, Q (f x)) (y : J) :
    Q (extend d p fill f y) := by
  unfold extend padded
  dsimp only [Function.comp_apply]
  split <;> first | exact hf _ | exact hfill

/-- In particular, padding may be performed before or after serializing each record. -/
theorem extend_map {I J A B : Type} {s : Shape} (d : Addr s s.D ≃ I) (p : Addr s s.E ≃ J)
    (F : A → B) (fill : A) (f : I → A) :
    extend d p (F fill) (F ∘ f) = F ∘ extend d p fill f := by
  funext y
  unfold extend padded
  dsimp only [Function.comp_apply]
  split <;> rfl

theorem extend_sized {I J : Type} {s : Shape} (d : Addr s s.D ≃ I) (p : Addr s s.E ≃ J)
    {w : ℕ} {fill : Tree} {f : I → Tree} (hfill : size fill ≤ w) (hf : ∀ x, size (f x) ≤ w) (y : J) :
    size (extend d p fill f y) ≤ w := extend_prop d p (fun z : Tree => size z ≤ w) hfill hf y

/-- Both register calls surrounding a native swap. They share one constant and one register cap, and
leave the parked deck intact. The equivalences specify the physical orders used by the caller. -/
theorem stripe_commands : ∃ R : ℕ, ∃ grow crop : Cmd, ∃ C : ℕ, Within R grow ∧ Within R crop ∧
    ∀ {I J : Type} (s : Shape) (_hs : Good s) (D : Series I) (E : Series J)
      (d : Adopt (series s s.D) D) (p : Adopt (series s s.E) E)
      (σ : I → I) (τ : J → J),
      (∀ x, σ (d.cast x) = d.cast (swap x)) → (∀ y, τ (p.cast y) = p.cast (swap y)) →
      ∀ w fill (f : I → Tree), size fill ≤ w → (∀ x, size (f x) ≤ w) →
      ∀ env r base, DeckCap base r →
      let time := C * (scanVolume s.volume w + 1)
      let g := extend d.cast p.cast fill f
      BoundedFits env grow (pile 0 (.fork (send s.header) (.fork (stripe D f) fill)) r)
        (pile 0 (stripe E g) r) time (base + time) time ∧
      BoundedFits env crop (pile 0 (.fork (send s.header) (stripe E (g ∘ τ))) r)
        (pile 0 (stripe D (f ∘ σ)) r) time (base + time) time := by
  obtain ⟨R,grow,crop,C,hgrow,hcrop,H⟩ := stream_commands
  refine ⟨R,grow,crop,C,hgrow,hcrop,?_⟩
  intro I J s hs D E d p σ τ hσ hτ w fill f hfill hf env r base hr
  let g := extend d.cast p.cast fill f
  have hg (y : J) : size (g y) ≤ w := extend_sized d.cast p.cast hfill hf y
  obtain ⟨H₁,H₂⟩ := H s hs w fill hfill env r base hr
  have HE : ∀ (v : J → Tree), stripe E v = send (stream (v ∘ p.cast)) := by
    intro v; rw [stripe_eq,p.route,series_tab]
  have HD : ∀ (v : I → Tree), stripe D v = send (stream (v ∘ d.cast)) := by
    intro v; rw [stripe_eq,d.route,series_tab]
  have hge : g ∘ p.cast = padded fill (f ∘ d.cast) := by funext y; simp [g,extend]
  have hgd : ((g ∘ τ) ∘ p.cast) ∘ embed hs.hDE = (f ∘ σ) ∘ d.cast := by
    funext x
    have hx : occupied (swap (embed hs.hDE x)) := ⟨x.2.2.2.1.isLt,x.2.1.isLt⟩
    simp only [Function.comp_apply,hτ,hσ,g,extend,Equiv.symm_apply_apply,padded,hx,↓reduceDIte]
    rfl
  constructor
  · rw [HD,HE,show extend d.cast p.cast fill f ∘ p.cast = _ from hge]
    exact H₁ (f ∘ d.cast) (fun x => hf _)
  · change BoundedFits _ _ (pile 0 (.fork _ (stripe E (g ∘ τ))) _) _ _ _ _
    rw [HE,HD,←hgd]
    exact H₂ ((g ∘ τ) ∘ p.cast) (fun x => hg _)

open IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom

/-- Literal binary and `b`-ary stock stripes on the two ends of each physical scan, with
no hidden field-order permutation. The expanded native interchange lies between these calls. -/
theorem native_commands : ∃ R : ℕ, ∃ grow crop : Cmd, ∃ C : ℕ, Within R grow ∧ Within R crop ∧
    ∀ (s : Shape) (_hs : Good s) (P G B : Tape) (b n e : ℕ)
      (hp : s.P = room P) (hg : s.G = room G) (hb : s.B = room B)
      (hd : s.D = 2^n) (he : s.E = b^e),
      let d := nativeView s s.D 2 n P G B hp hg hb hd
      let p := nativeView s s.E b e P G B hp hg hb he
      ∀ w fill (f : SpanKey P G B (Block 2 n) → Tree), size fill ≤ w → (∀ x, size (f x) ≤ w) →
      ∀ env r base, DeckCap base r →
      let time := C * (scanVolume s.volume w + 1)
      let g := extend d.cast p.cast fill f
      BoundedFits env grow (pile 0 (.fork (send s.header) (.fork (stripe (stock 2 P G B n) f) fill)) r)
        (pile 0 (stripe (stock b P G B e) g) r) time (base + time) time ∧
      BoundedFits env crop (pile 0 (.fork (send s.header) (stripe (stock b P G B e) (g ∘ swapper P G B))) r)
        (pile 0 (stripe (stock 2 P G B n) (f ∘ swapper P G B)) r) time (base + time) time := by
  obtain ⟨R,grow,crop,C,hgrow,hcrop,H⟩ := stripe_commands
  refine ⟨R,grow,crop,C,hgrow,hcrop,?_⟩
  intro s hs P G B b n e hp hg hb hd he
  exact H s hs (stock 2 P G B n) (stock b P G B e) _ _ _ _
    (fun x => (nativeView_swap hp hg hb hd x).symm) (fun y => (nativeView_swap hp hg hb he y).symm)

end BinaryHalo

end NearSquareRoot
end Computability
end OAI
