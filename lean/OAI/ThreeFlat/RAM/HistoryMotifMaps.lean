import OAI.ThreeFlat.RAM.PhysicalPinsNat
import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # Fixed ROM for the pin maps inside a histogram party

The four mapping cases refer to a tile, payload compactor, histogram test,
and histogram counter. The number of copies, cutoff, symbol count and header
arity are ordinary machine data. None occurs in the instruction syntax.
-/

namespace ThreeFlat.RAM.HistoryMotifMaps

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr
open scoped Fin.CommRing

inductive Kind where | tile | stream | localTest | counter deriving DecidableEq

def Kind.tag : Kind → ℕ | .tile=>0 | .stream=>1 | .localTest=>2 | .counter=>3

/-- Operand words in order are kind, input pin, component ordinal, copies,
per-copy header arity, ports, maximum per-copy width, letters and quota.
Within the last two cases the header arity counts all port selector bits. -/
def values (kind : Kind) (x i r b e d h quota : ℕ) : Fin 9 → ℕ := ![kind.tag,x,i,r,b,e,d,h,quota]

private abbrev Form := Formula 9
private abbrev R (i : Fin 9) : Form := .reg i

private def tile : Form :=
  let pin := R 1; let copy := R 2; let r := R 3; let b := R 4; let e := R 5; let d := R 6
  let bank := mul e (mul r d)
  let side := mul e d
  let rest := sub pin b
  let offset (j : Form) := add (add (mul (mul r d) (div j d)) (mul d copy)) (rem j d)
  let hidden := add (L 2) (add (mul r b) bank)
  lt pin b (add (L 2) (add (mul b copy) pin))
    (lt rest side (add hidden (offset rest)) (add (add hidden bank) (offset (sub rest side))))

private def stream : Form :=
  let pin := R 1; let port := R 2; let r := R 3; let b := R 4; let e := R 5; let d := R 6
  let stride := mul r d; let bank := mul e stride; let offset := mul stride port
  let hidden := add (L 2) (add (mul r b) bank)
  lt pin stride (add hidden (add offset pin))
    (lt (sub pin stride) stride (add (add hidden bank) (add offset (sub pin stride)))
      (add (add (L 2) (mul r b)) (add offset (sub (sub pin stride) stride))))

private def localTest : Form :=
  let pin := R 1; let copy := R 2; let r := R 3; let b := R 4; let h := R 7
  lt pin b (add (L 2) (add (mul b copy) pin)) (add (add (L 2) (mul r b)) (add (mul h copy) (sub pin b)))

private def counter : Form :=
  let pin := R 1; let letter := R 2; let r := R 3; let b := R 4; let h := R 7
  lt pin r (add (add (L 2) (mul r b)) (add (mul h pin) letter))
    (lt (sub pin r) r (L 1) (lt (sub (sub pin r) r) (R 8) (L 1) (L 0)))

def formula : Formula 9 := lt (R 0) (L 2) (eqz (R 0) (L 0) tile stream) (eqz (R 0) (L 2) localTest counter)

def word (kind : Kind) (x i r b e d h quota : ℕ) : ℕ :=
  let bank := e*(r*d)
  let hidden := 2+(r*b+bank)
  match kind with
  | .tile =>
    let offset (j : ℕ) := (r*d)*(j/d)+d*i+j%d
    if x<b then 2+(b*i+x) else if x-b<e*d then hidden+offset (x-b) else (hidden+bank)+offset ((x-b)-e*d)
  | .stream => if x<r*d then hidden+((r*d)*i+x) else if x-r*d<r*d then hidden+bank+((r*d)*i+(x-r*d))
      else 2+r*b+((r*d)*i+((x-r*d)-r*d))
  | .localTest => if x<b then 2+(b*i+x) else 2+r*b+(h*i+(x-b))
  | .counter => if x<r then 2+r*b+(h*x+i) else if x-r<r then 1 else if (x-r)-r<quota then 1 else 0

theorem natural (W : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (kind : Kind) (x i r b e d h quota : ℕ) :
    formula.natural W data mem (values kind x i r b e d h quota) = word kind x i r b e d h quota := by
  cases kind <;>
    simp [formula,values,word,tile,stream,localTest,counter,Kind.tag,Formula.natural,natOp,natTest]
  case tile =>
    by_cases first : x < b <;> by_cases second : x-b < e*d <;> simp [first,second]
  case stream =>
    by_cases first : x < r*d <;> by_cases second : x-r*d < r*d <;> simp [first,second]
  case localTest =>
    by_cases first : x < b <;> simp [first]
  case counter =>
    by_cases first : x < r <;> by_cases second : x-r < r <;>
      by_cases third : x-r-r < quota <;> simp [first,second,third]

set_option maxHeartbeats 800000 in
/-- Exact-address arithmetic for the native pin map. Multiplication and addition
in the final source address agree modulo the word width. Comparisons, truncated
differences and divisions use the bounded pin, stride and quota operands. -/
theorem fits_values (W : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ)
    (kind : Kind) (x i r b e d h quota : ℕ)
    (four : 4<2^W) (pin : x<2^W) (copies : r<2^W) (head : b<2^W) (digit : d<2^W)
    (side : e*d<2^W) (stripe : r*d<2^W) (count : quota<2^W) :
    formula.Fits W data mem (values kind x i r b e d h quota) := by
  have xb : x-b<2^W := (Nat.sub_le ..).trans_lt pin
  have xr : x-r<2^W := (Nat.sub_le ..).trans_lt pin
  have xd : x-(r*d)<2^W := (Nat.sub_le ..).trans_lt pin
  have xs : (x-b)-(e*d)<2^W := (Nat.sub_le ..).trans_lt xb
  have xrr : (x-r)-r<2^W := (Nat.sub_le ..).trans_lt xr
  have xdd : (x-r*d)-r*d<2^W := (Nat.sub_le ..).trans_lt xd
  have constants : 0<2^W ∧ 1<2^W ∧ 2<2^W ∧ 3<2^W := by omega
  rcases constants with ⟨zero,one,two,three⟩
  cases kind <;>
    simp [formula,tile,stream,localTest,counter,values,Kind.tag,Formula.Fits,Formula.natural,
      opFits,natOp,natTest,zero,one,two,three,pin,copies,head,digit,side,stripe,count,xb,xr,xd,xs,xrr];
    intros; by_cases final : x-r-r < quota <;> simp [final]

def program (W : ℕ) : Term W 1 9 := formula.compile (fun _ => 0)

theorem binds (W : ℕ) : (program W).binds ≤ 300 := by rw [program,Formula.binds_compile]; decide +kernel

theorem eval (W : ℕ) (data : Fin 1 → ℕ) (mem : ℕ → ℕ) (kind : Kind) (x i r b e d h quota : ℕ)
    (room : formula.Fits W (fun _ => data 0) mem (values kind x i r b e d h quota)) :
    (program W).eval (fun j => (data j : Word W)) (fun j => (mem j : Word W))
      (fun j => (values kind x i r b e d h quota j : Word W)) = (word kind x i r b e d h quota : Word W) := by
  rw [program,Formula.eval_compile]
  exact (Formula.value_eq_natural formula (fun _ => data 0) mem _ room).trans
    (congrArg (fun v : ℕ => (v : Word W)) (natural W _ mem kind x i r b e d h quota))


end ThreeFlat.RAM.HistoryMotifMaps

end OAI
