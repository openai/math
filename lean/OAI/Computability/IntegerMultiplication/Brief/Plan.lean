import OAI.Computability.IntegerMultiplication.Carry.Figure
import OAI.Computability.IntegerMultiplication.Param.Cut
import OAI.Computability.IntegerMultiplication.Param.Space

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Brief
open Code Strip Carry Bits Staff Param
variable {I : Type} {r : Regime I} (n : I→ℕ)
structure Guide (r : Regime I) (n:I→ℕ) : Prop where
  amount_ : Figure r n

namespace Guide
variable (g:Guide r n)
include g
omit g in
theorem soft (m:I→ℕ) (h:Figure r m) : Realizes r (fun i=> Nat.clog 2 (m i)) := h.short_log
omit g in
theorem maximize {m t:I→ℕ} (h:Realizes r m) (v:Realizes r t) :
    Realizes r (fun i=>max (m i) (t i)) := by
  simpa only [max_def_lt] using v.select h (h.below v)
theorem logarithm : Realizes r (beta ∘ n) :=
  maximize (.fix _) g.amount_.short_log
theorem neck : Realizes r (height ∘ n) :=
  let z := Realizes.times (.fix 4) (g.logarithm n)
  Realizes.plus (Realizes.dividing
    (Figure.short_log (Figure.of_spoken z)) (.fix 32)) (.fix 1)

private theorem cap :
    Dom r.scale (budget ∘ n) :=
  let u := ((Dom.const _ (2^36)).mul (Staff.diameter _ (g.logarithm n)))
  u.mono (fun _i=>beyond _)
theorem spread : Realizes r (lanes ∘ n) :=
  ((Figure.natural 2).repeated (g.neck n)).pay
    ((g.cap n).mono (fun i=>Nat.le_self_pow (by decide) _ : ∀ i,(lanes ∘ n) i≤(budget ∘ n) i))
theorem fund : Realizes r (budget ∘ n) :=
  ((Figure.of_spoken (g.spread n)).repeated (.fix 32)).pay (g.cap n)

theorem raise_ : Figure r (amount ∘ n) := by
  let x := Figure.of_spoken (g.fund n)
  exact ((g.amount_.added x).subtracted (.natural 1)).quotients x
theorem exSize :
    Realizes r (total ∘ n) :=
  ((Figure.natural 4).multiplied (g.raise_ n)).short_log
theorem tensorSize :
    Realizes r (span_ ∘ n) :=
  let t := g.spread n
  (((g.exSize n).plus t).minused (.fix 1)).dividing t
theorem missing :
    Realizes r (slack ∘ n) :=
  ((g.spread n).times (g.tensorSize n)).minused (g.exSize n)
theorem reducedTensor :
    Realizes r (reach ∘ n) :=
  (g.tensorSize n).minused (g.missing n)
theorem generator :
    Realizes r (chunk ∘ n) :=
  ((Figure.natural 2).repeated ((g.neck n).dividing (.fix giant))).pay
    ((diameter _ (g.spread n)).mono (fun i=>chunk_l (n i)))
theorem positions :
    Realizes r (scouts ∘ n) :=
  (g.spread n).minused (.fix 2)
theorem jumps :
    Realizes r (batches ∘ n) :=
  ((g.tensorSize n).dividing (g.generator n)).minused (.fix 1)
theorem excess :
    Realizes r (border ∘ n) :=
  (g.generator n).plus ((g.tensorSize n).rem (g.generator n))
theorem vision :
    Realizes r (facing ∘ n) :=
  (g.positions n).times (g.tensorSize n)
theorem depth :
    Realizes r (faces ∘ n) :=
  (g.vision n).dividing (g.generator n)
theorem mod_ :
    Realizes r (trace_ ∘ n) :=
  (g.vision n).rem (g.generator n)

-- individual axis data in polynomial directories p
theorem side_long : Figure r (wall ∘ n) :=
  (Figure.natural 2).repeated (g.tensorSize n)
theorem side_short : Figure r (room ∘ n) :=
  (Figure.natural 2).repeated (g.reducedTensor n)
theorem root :
    Figure r (nugget ∘ n) := by
  let d := Figure.of_spoken (g.spread n)
  let t := g.side_short n
  let c := (Figure.natural 8).multiplied d
  let b := Figure.natural (r:=r)
  let S := (((c.subtracted (b 1)).multiplied t).quotients c).rooted
  exact (b 1).maximum (((b 2).multiplied (S.quotients (b 2))).subtracted (b 1))
theorem D :
    Figure r (fun i=> red (lanes (n i)) (nugget (n i))) :=
  ((Figure.natural 2).multiplied (Figure.fact (g.spread n))).multiplied (g.root n)
theorem section_ :
    Figure r (fun i=> lift_ (lanes (n i)) (wall (n i)) (red (lanes (n i)) (nugget (n i)))) := by
  let c := (Figure.natural 8).multiplied (Figure.of_spoken (g.spread n))
  exact (((c.subtracted (.natural 2)).multiplied (g.side_long n)).quotients
    (c.multiplied (g.D n))).added (.natural 1)

variable {x:I→ℕ} (h:Realizes r x)
include h
theorem shorten :
    Classified r (fun i=>Param.short (n i) (x i)) := by
  let z := g.positions n
  have t := (Regime.Has.pair (g:=fun i=>tally (x i)) (f:=fun i=>tally (abbreviated (n i))) h z).ez
    (Iter.linked (X:=Unit) (Y:=Unit))
  simp only [tally_length] at t
  exact ⟨_,t,fun _=>by simp [Param.short]⟩
theorem radix_ :
    Realizes r (fun i=> axle (n i) (x i)) :=
  Realizes.select (g.reducedTensor n) (g.tensorSize n) (g.shorten n h)
theorem length_ :
    Figure r (fun i=> side (n i) (x i)) :=
  (Figure.natural 2).repeated (g.radix_ n h)
theorem size_ :
    Figure r (fun i=> moduli (n i) (x i)) :=
  Figure.variant ((g.root n).repeated (.fix 2))
    ((((g.section_ n).added (Figure.of_spoken h)).multiplied (g.D n)).added (.natural 1))
    (g.shorten n h)

-- extension to tally loop
theorem abroad :
    Guide (signal x h) (n ∘ (Sigma.fst : Across x→I)) := by
  obtain ⟨v,e,i⟩ := g.amount_
  exact ⟨v ∘ Staff.at_ x,sendRoof x h _ e,fun a=>i a.1⟩
end Guide
end Brief

end IntegerMultiplication
end Computability
end OAI
