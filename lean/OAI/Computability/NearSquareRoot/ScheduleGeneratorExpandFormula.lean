import OAI.Computability.NearSquareRoot.ScheduleGeneratorAlphabetDigits
import Mathlib.Computability.Partrec

/-! # Numeric transition formulas for public input expansion -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.ExpandRows
open CommonAlphabet.Numbering

/-- Command tuple for the two tapes. Each command has three possible movements
per letter, and the first tape supplies the least significant digit. -/
def commands (src dst s d : ℕ) := (s+3*src) + 12*(d+3*dst)

def embedDigit (k : ℕ) := if k=0 then 0 else k+1

def rowCore (size w bit0 bit1 sep : ℕ) (enc : ℕ × ℕ → ℕ) (q src dst : ℕ) :
    Option (ℕ × ℕ) :=
  let p := q-3
  let bound := size*w
  let parsed := if src=1 then sep else if src=2 then bit0 else bit1
  if q=0 then
    if src=0 then some (1, commands src dst 0 1)
    else some (w*parsed+3, commands src dst 2 1)
  else if q=1 then
    if src=0 then some (2, commands src dst 2 1)
    else some (bound+3, commands src dst 0 1)
  else if q=2 then none
  else if p < bound then
    some (if p%w+1 < w then q+1 else 0, commands src (embedDigit (enc (p/w,p%w))) 1 2)
  else some (if p-bound+1 < w then q+1 else 1, commands src dst 1 0)

def row (size w bit0 bit1 sep : ℕ) (enc : ℕ × ℕ → ℕ) (p : ℕ × ℕ) :
    Option (ℕ × ℕ) :=
  rowCore size w bit0 bit1 sep enc p.1 (digit 4 p.2 0) (digit 4 p.2 1)

private theorem compIf {X Y : Type} [Primcodable X] [Primcodable Y]
    {p : X → Prop} [DecidablePred p] {f g : X → Y} (h : Computable fun x => decide (p x))
    (hf : Computable f) (hg : Computable g) : Computable fun x => if p x then f x else g x :=
  (Computable.cond h hf hg).of_eq fun _ => by simp

private theorem compCommands {X : Type} [Primcodable X] {s d a b : X → ℕ}
    (hs : Computable s) (hd : Computable d) (ha : Computable a) (hb : Computable b) :
    Computable fun x => commands (s x) (d x) (a x) (b x) :=
  Primrec.nat_add.to_comp.comp (Primrec.nat_add.to_comp.comp ha (Primrec.nat_mul.to_comp.comp
    (Computable.const 3) hs)) (Primrec.nat_mul.to_comp.comp (Computable.const 12)
      (Primrec.nat_add.to_comp.comp hb (Primrec.nat_mul.to_comp.comp (Computable.const 3) hd)))

private theorem compDigit (k : ℕ) : Computable fun n => digit 4 n k :=
  (primrec_digit (Primrec.const 4) Primrec.id (Primrec.const k)).to_comp

private theorem compEmbed : Computable embedDigit :=
  compIf (Primrec.eq.decide.to_comp.comp Computable.id (Computable.const 0)) (Computable.const 0)
    (Primrec.nat_add.to_comp.comp Computable.id (Computable.const 1))

theorem computable_row {size w bit0 bit1 sep : ℕ → ℕ} {enc : ℕ → ℕ × ℕ → ℕ}
    (ha : Computable size) (hw : Computable w) (hb₀ : Computable bit0) (hb₁ : Computable bit1)
    (hs : Computable sep) (he : Computable₂ enc) :
    Computable₂ (fun j => row (size j) (w j) (bit0 j) (bit1 j) (sep j) (enc j)) := by
  let X := ℕ × (ℕ × ℕ)
  let q (v : X) := v.2.1
  let src (v : X) := digit 4 v.2.2 0
  let dst (v : X) := digit 4 v.2.2 1
  have hq : Computable q := Computable.fst.comp Computable.snd
  have src' : Computable src := (compDigit 0).comp (Computable.snd.comp Computable.snd)
  have dst' : Computable dst := (compDigit 1).comp (Computable.snd.comp Computable.snd)
  let b (v : X) := size v.1 * w v.1
  let p (v : X) := q v - 3
  have hw' : Computable fun v : X => w v.1 := hw.comp Computable.fst
  have b' : Computable b := Primrec.nat_mul.to_comp.comp (ha.comp Computable.fst) hw'
  have p' : Computable p := Primrec.nat_sub.to_comp.comp hq (Computable.const 3)
  let parsed (v : X) := if src v=1 then sep v.1 else if src v=2 then bit0 v.1 else bit1 v.1
  have parsed' : Computable parsed :=
    compIf (Primrec.eq.decide.to_comp.comp src' (Computable.const 1)) (hs.comp Computable.fst)
      (compIf (Primrec.eq.decide.to_comp.comp src' (Computable.const 2))
        (hb₀.comp Computable.fst) (hb₁.comp Computable.fst))
  have div' := Primrec.nat_div.to_comp.comp p' hw'
  have mod' := Primrec.nat_mod.to_comp.comp p' hw'
  have increment := Primrec.nat_add.to_comp.comp hq (Computable.const 1)
  have nextEmit : Computable fun v : X => if p v % w v.1+1 < w v.1 then q v+1 else 0 :=
    compIf (Primrec.nat_lt.decide.to_comp.comp (Primrec.nat_add.to_comp.comp mod' (Computable.const 1))
      hw') increment (Computable.const 0)
  have nextSkip : Computable fun v : X => if p v-b v+1 < w v.1 then q v+1 else 1 :=
    compIf (Primrec.nat_lt.decide.to_comp.comp
      (Primrec.nat_add.to_comp.comp (Primrec.nat_sub.to_comp.comp p' b') (Computable.const 1)) hw')
      increment (Computable.const 1)
  have read0 := Primrec.eq.decide.to_comp.comp src' (Computable.const 0)
  let act (x s d : ℕ) (v : X) := some (x, commands (src v) (dst v) s d)
  have act' (x s d : ℕ) : Computable (act x s d) :=
    Computable.option_some.comp ((Computable.const x).pair (compCommands src' dst'
      (Computable.const s) (Computable.const d)))
  exact compIf (Primrec.eq.decide.to_comp.comp hq (Computable.const 0))
    (compIf read0 (act' 1 0 1)
      (Computable.option_some.comp ((Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp
        hw' parsed') (Computable.const 3)).pair (compCommands src' dst' (Computable.const 2) (Computable.const 1)))))
    (compIf (Primrec.eq.decide.to_comp.comp hq (Computable.const 1))
      (compIf read0 (act' 2 2 1)
        (Computable.option_some.comp ((Primrec.nat_add.to_comp.comp b' (Computable.const 3)).pair
          (compCommands src' dst' (Computable.const 0) (Computable.const 1)))))
      (compIf (Primrec.eq.decide.to_comp.comp hq (Computable.const 2)) (Computable.const none)
        (compIf (Primrec.nat_lt.decide.to_comp.comp p' b')
          (Computable.option_some.comp (nextEmit.pair (compCommands src'
            (compEmbed.comp (he.comp Computable.fst (div'.pair mod'))) (Computable.const 1) (Computable.const 2))))
          (Computable.option_some.comp (nextSkip.pair (compCommands src' dst' (Computable.const 1) (Computable.const 0)))))))

end Generator.ExpandRows

end NearSquareRoot
end Computability
end OAI
