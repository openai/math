import OAI.Computability.NearSquareRoot.ScheduleGeneratorStackFormula

/-! # Numeric transitions for the public output compactor -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.CompactRows

open CommonAlphabet.Numbering

def scanCount (w : ℕ) := 3^w*w

def scanState (w buf j : ℕ) := j + w*buf + 2
def emitState (w d : ℕ) := scanCount w+d+2
def backState (w j : ℕ) := scanCount w+(3+j)+2

/-- Replace the digit of a finite buffer, retaining all other digits. -/
def storeDigit (w buf j v : ℕ) :=
  encodeBase 3 ((List.range w).map fun k => if k=j then v else digit 3 buf k)

/-- Two tape instructions, in source then destination order. -/
def operations (src dst srcMove dstMove : ℕ) :=
  (srcMove+3*src) + 12*(dstMove+3*dst)

def row (w : ℕ) (decode : ℕ → ℕ) (p : ℕ × ℕ) : Option (ℕ × ℕ) :=
  let src := digit 4 p.2 0
  let dst := digit 4 p.2 1
  let move (q i j : ℕ) := some (q,operations src dst i j)
  let body := p.1-2
  let tail := body-scanCount w
  if p.1 = 0 then
    if dst = 0 then move 1 1 2 else move (backState w 0) 1 0
  else if p.1 = 1 then none
  else if body < scanCount w then
    let idx := body%w
    let buf := storeDigit w (body/w) idx (src-1)
    let dest := if idx+1 < w then scanState w buf (idx+1) else emitState w (decode buf)
    move dest 2 1
  else if tail < 3 then
    if tail = 0 then move (backState w 0) 1 0
    else some (scanState w 0 0,operations src (tail+1) 1 2)
  else
    let idx := tail-3
    move (if idx+1 < w then backState w (idx+1) else 0) 0 1

variable {X : Type} [Primcodable X]

private theorem scanCount_eff {w : X → ℕ} (hw : Primrec w) : Primrec fun x => scanCount (w x) :=
  Primrec.nat_mul.comp (KernelComputableAddress.primrec_pow (Primrec.const 3) hw) hw

private theorem scanState_eff {w b j : X → ℕ} (hw : Primrec w) (hb : Primrec b)
    (hj : Primrec j) : Primrec fun x => scanState (w x) (b x) (j x) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp hj (Primrec.nat_mul.comp hw hb)) (Primrec.const 2)

private theorem emitState_eff {w d : X → ℕ} (hw : Primrec w) (hd : Primrec d) :
    Primrec fun x => emitState (w x) (d x) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (scanCount_eff hw) hd) (Primrec.const 2)

private theorem backState_eff {w j : X → ℕ} (hw : Primrec w) (hj : Primrec j) :
    Primrec fun x => backState (w x) (j x) :=
  emitState_eff hw (Primrec.nat_add.comp (Primrec.const 3) hj)

theorem primrec_storeDigit {w b j v : X → ℕ} (hw : Primrec w) (hb : Primrec b)
    (hj : Primrec j) (hv : Primrec v) : Primrec fun x => storeDigit (w x) (b x) (j x) (v x) :=
  primrec_encodeBase.comp (Primrec.const 3) (Primrec.list_map (Primrec.list_range.comp hw)
    (Primrec.ite (Primrec.eq.comp Primrec.snd (hj.comp Primrec.fst)) (hv.comp Primrec.fst)
      (primrec_digit (Primrec.const 3) (hb.comp Primrec.fst) Primrec.snd)).to₂)

private theorem operations_eff {s d i j : X → ℕ} (hs : Primrec s) (hd : Primrec d)
    (hi : Primrec i) (hj : Primrec j) : Primrec fun x => operations (s x) (d x) (i x) (j x) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp hi (Primrec.nat_mul.comp (Primrec.const 3) hs))
    (Primrec.nat_mul.comp (Primrec.const 12) (Primrec.nat_add.comp hj (Primrec.nat_mul.comp (Primrec.const 3) hd)))

/-- Every branch of a numeric compactor row is primitive recursive when the block
classification is supplied as an argument. Only its value on the newly scanned buffer is used. -/
private theorem row_eff {w s top d : X → ℕ} (hw : Primrec w) (hs : Primrec s)
    (ht : Primrec top) (hd : Primrec d) :
    Primrec fun x => row (w x) (fun _ => d x) (s x,top x) := by
  let src x := digit 4 (top x) 0
  let dst x := digit 4 (top x) 1
  let body x := s x-2
  let tail x := body x-scanCount (w x)
  let idx x := body x % w x
  let buf x := storeDigit (w x) (body x/w x) (idx x) (src x-1)
  let go (next sm dm : X → ℕ) x := some (next x,operations (src x) (dst x) (sm x) (dm x))
  have srcE : Primrec src := primrec_digit (Primrec.const 4) ht (Primrec.const 0)
  have dstE : Primrec dst := primrec_digit (Primrec.const 4) ht (Primrec.const 1)
  have goE {next sm dm : X → ℕ} (h : Primrec next) (i : Primrec sm) (j : Primrec dm) :
      Primrec (go next sm dm) := Primrec.option_some.comp (h.pair (operations_eff srcE dstE i j))
  have bodyE : Primrec body := Primrec.nat_sub.comp hs (Primrec.const 2)
  have tailE : Primrec tail := Primrec.nat_sub.comp bodyE (scanCount_eff hw)
  have idxE : Primrec idx := Primrec.nat_mod.comp bodyE hw
  have bufE : Primrec buf := primrec_storeDigit hw (Primrec.nat_div.comp bodyE hw) idxE
    (Primrec.nat_sub.comp srcE (Primrec.const 1))
  have prev := Primrec.ite (Primrec.eq.comp dstE (Primrec.const 0))
    (goE (Primrec.const 1) (Primrec.const 1) (Primrec.const 2))
    (goE (backState_eff hw (Primrec.const 0)) (Primrec.const 1) (Primrec.const 0))
  have scan := goE (Primrec.ite (Primrec.nat_lt.comp (Primrec.succ.comp idxE) hw)
    (scanState_eff hw bufE (Primrec.succ.comp idxE)) (emitState_eff hw hd))
    (Primrec.const 2) (Primrec.const 1)
  have emit := Primrec.ite (Primrec.eq.comp tailE (Primrec.const 0))
    (goE (backState_eff hw (Primrec.const 0)) (Primrec.const 1) (Primrec.const 0))
    (Primrec.option_some.comp ((scanState_eff hw (Primrec.const 0) (Primrec.const 0)).pair
      (operations_eff srcE (Primrec.succ.comp tailE) (Primrec.const 1) (Primrec.const 2))))
  have next := Primrec.succ.comp (Primrec.nat_sub.comp tailE (Primrec.const 3))
  have back := goE (Primrec.ite (Primrec.nat_lt.comp next hw) (backState_eff hw next) (Primrec.const 0))
    (Primrec.const 0) (Primrec.const 1)
  exact Primrec.ite (Primrec.eq.comp hs (Primrec.const 0)) prev (Primrec.ite
    (Primrec.eq.comp hs (Primrec.const 1)) (Primrec.const none) (Primrec.ite
      (Primrec.nat_lt.comp bodyE (scanCount_eff hw)) scan (Primrec.ite
        (Primrec.nat_lt.comp tailE (Primrec.const 3)) emit back)))

theorem computable_row {w : ℕ → ℕ} {decode : ℕ → ℕ → ℕ}
    (hw : Computable w) (hd : Computable₂ decode) :
    Computable₂ (fun j p => row (w j) (decode j) p) := by
  let buf (v : ℕ × (ℕ × ℕ)) :=
    storeDigit v.1 ((v.2.1-2)/v.1) ((v.2.1-2)%v.1) (digit 4 v.2.2 0-1)
  have s : Primrec fun p : ℕ × (ℕ × ℕ) => p.2.1-2 :=
    Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2)
  have hb : Primrec buf := primrec_storeDigit Primrec.fst (Primrec.nat_div.comp s Primrec.fst)
    (Primrec.nat_mod.comp s Primrec.fst) (Primrec.nat_sub.comp
      (primrec_digit (Primrec.const 4) (Primrec.snd.comp Primrec.snd) (Primrec.const 0)) (Primrec.const 1))
  have args := (hw.comp Computable.fst).pair (Computable.snd (α := ℕ) (β := ℕ × ℕ))
  have cls := hd.comp Computable.fst (hb.to_comp.comp args)
  have raw := (row_eff (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to_comp.comp (args.pair cls)
  apply raw.of_eq
  intro p
  dsimp [row,buf]

end Generator.CompactRows

end NearSquareRoot
end Computability
end OAI
