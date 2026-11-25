import OAI.Computability.NearSquareRoot.ScheduleGeneratorAlphabetDigits
import Mathlib.Computability.Partrec

/-! # Effective numeric transitions of the two-phase stack compiler -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.StackRows
open CommonAlphabet.Numbering

/-- Actions have ranks `skip=0`, `pop=1` and `push(a)=2+rank(a)`. The
instruction rank equals the movement rank plus three times the new letter rank. -/
def first (act top : ℕ) : ℕ :=
  if act=0 then 1+3*top else if act=1 then (if top=0 then 1 else 2) else 3*top

def second (act top : ℕ) : ℕ := 1+3*(if 2 ≤ act then act-1 else top)

def cmds (f : ℕ → ℕ → ℕ) (a i acts tops : ℕ) : ℕ :=
  encodeBase ((a+1)*3) ((List.range i).map fun k =>
    f (digit (a+2) acts k) (digit (a+1) tops k))

/-- One row of the compiled tape machine, given one row function of the source
stack machine. `a`, `q` and `i` count the source letters, states and tapes. -/
def row (a q i : ℕ) (orig : ℕ × ℕ → Option (ℕ × ℕ)) (p : ℕ × ℕ) : Option (ℕ × ℕ) :=
  let b := (a+2)^i
  if p.1 < q then
    (orig p).map fun z => (q + (z.2+b*z.1), cmds first a i z.2 p.2)
  else
    let z := p.1-q
    some (z/b, cmds second a i (z%b) p.2)

theorem primrec_first : Primrec₂ first := by
  have hm : Primrec fun v : ℕ × ℕ => 3*v.2 := Primrec.nat_mul.comp (Primrec.const 3) Primrec.snd
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.nat_add.comp (Primrec.const 1) hm)
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
      (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 1) (Primrec.const 2)) hm)

theorem primrec_second : Primrec₂ second :=
  Primrec.nat_add.comp (Primrec.const 1) (Primrec.nat_mul.comp (Primrec.const 3)
    (Primrec.ite (Primrec.nat_le.comp (Primrec.const 2) Primrec.fst)
      (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)) Primrec.snd))

variable {X : Type} [Primcodable X]

theorem primrec_cmds {f : ℕ → ℕ → ℕ} (hf : Primrec₂ f)
    {a i acts tops : X → ℕ} (ha : Primrec a) (hi : Primrec i) (hc : Primrec acts) (ht : Primrec tops) :
    Primrec fun x => cmds f (a x) (i x) (acts x) (tops x) :=
  primrec_encodeBase.comp
    (Primrec.nat_mul.comp (Primrec.nat_add.comp ha (Primrec.const 1)) (Primrec.const 3))
    (Primrec.list_map (Primrec.list_range.comp hi)
      (hf.comp
        (primrec_digit (Primrec.nat_add.comp (ha.comp Primrec.fst) (Primrec.const 2))
          (hc.comp Primrec.fst) Primrec.snd)
        (primrec_digit (Primrec.nat_add.comp (ha.comp Primrec.fst) (Primrec.const 1))
          (ht.comp Primrec.fst) Primrec.snd)).to₂)

theorem computable_cmds {f : ℕ → ℕ → ℕ} (hf : Primrec₂ f)
    {a i acts tops : X → ℕ} (ha : Computable a) (hi : Computable i)
    (hc : Computable acts) (ht : Computable tops) :
    Computable fun x => cmds f (a x) (i x) (acts x) (tops x) :=
  (primrec_cmds hf Primrec.fst (Primrec.fst.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to_comp.comp (ha.pair (hi.pair (hc.pair ht)))

/-- Uniform computability of the tape compiler for varying state, tape, and letter counts. -/
theorem computable_row {a q i : ℕ → ℕ} {orig : ℕ → ℕ × ℕ → Option (ℕ × ℕ)}
    (ha : Computable a) (hq : Computable q) (hi : Computable i) (hm : Computable₂ orig) :
    Computable₂ (fun j p => row (a j) (q j) (i j) (orig j) p) := by
  let b j := (a j+2)^i j
  have hb : Computable b := (KernelComputableAddress.primrec_pow
    (Primrec.nat_add.comp Primrec.fst (Primrec.const 2)) Primrec.snd).to_comp.comp (ha.pair hi)
  let X := ℕ × (ℕ × ℕ)
  have state : Computable fun p : X => p.2.1 := Computable.fst.comp Computable.snd
  have top : Computable fun p : X => p.2.2 := Computable.snd.comp Computable.snd
  let z (p : X) := p.2.1 - q p.1
  have hz : Computable z := Primrec.nat_sub.to_comp.comp state (hq.comp Computable.fst)
  have h₀ : Computable fun p : X => (orig p.1 p.2).map fun r =>
      (q p.1+(r.2+b p.1*r.1),cmds first (a p.1) (i p.1) r.2 p.2.2) := by
    apply Computable.option_map hm
    let idx : X × (ℕ × ℕ) → ℕ := fun v => v.1.1
    have j : Computable idx := Computable.fst.comp Computable.fst
    have l : Computable fun v : X × (ℕ × ℕ) => v.2.1 := Computable.fst.comp Computable.snd
    have r : Computable fun v : X × (ℕ × ℕ) => v.2.2 := Computable.snd.comp Computable.snd
    exact (Primrec.nat_add.to_comp.comp (hq.comp j) (Primrec.nat_add.to_comp.comp r
      (Primrec.nat_mul.to_comp.comp (hb.comp j) l))).pair
      (computable_cmds primrec_first (ha.comp j) (hi.comp j) r (top.comp Computable.fst))
  have h₁ : Computable fun p : X => some (z p / b p.1,
      cmds second (a p.1) (i p.1) (z p % b p.1) p.2.2) :=
    Computable.option_some.comp ((Primrec.nat_div.to_comp.comp hz (hb.comp Computable.fst)).pair
      (computable_cmds primrec_second (ha.comp Computable.fst) (hi.comp Computable.fst)
        (Primrec.nat_mod.to_comp.comp hz (hb.comp Computable.fst)) top))
  exact (Computable.cond (Primrec.nat_lt.decide.to_comp.comp state (hq.comp Computable.fst))
    h₀ h₁).of_eq fun p => by simp [row,b,z]

end Generator.StackRows

end NearSquareRoot
end Computability
end OAI
