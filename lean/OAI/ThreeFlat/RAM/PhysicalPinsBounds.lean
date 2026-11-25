import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # Static word-width bounds for physical pin and guard descriptors

Each magnitude is represented by an upper bound on its bit length. A loaded
word can use the full machine width. Every address and comparison operand
needed by the four fixed formulas uses at most four times the shape width
plus a fixed additive constant.
-/

namespace ThreeFlat.RAM.PhysicalPinsExpr

open Computability.VPVNP.BurstRAM PrivateRAM

namespace Estimate

structure Bits where
  shape : ℕ := 0
  word : ℕ := 0
  extra : ℕ := 0
  deriving DecidableEq

def Bits.total (b w : ℕ) (x : Bits) := x.shape*b+x.word*w+x.extra
def Bits.join (x y : Bits) : Bits :=
  ⟨max x.shape y.shape,max x.word y.word,max x.extra y.extra⟩
def Bits.add (x y : Bits) : Bits := ⟨x.shape+y.shape,x.word+y.word,x.extra+y.extra⟩
def Bits.more (x : Bits) : Bits := {x with extra := x.extra+1}

theorem total_left (b w : ℕ) (x y : Bits) :
    x.total b w ≤ (x.join y).total b w := by
  simp only [Bits.total,Bits.join]
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right b (le_max_left _ _))
    (Nat.mul_le_mul_right w (le_max_left _ _))) (le_max_left _ _)

theorem total_right (b w : ℕ) (x y : Bits) :
    y.total b w ≤ (x.join y).total b w := by
  simp only [Bits.total,Bits.join]
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right b (le_max_right _ _))
    (Nat.mul_le_mul_right w (le_max_right _ _))) (le_max_right _ _)

theorem total_add (b w : ℕ) (x y : Bits) :
    (x.add y).total b w=x.total b w+y.total b w := by
  simp [Bits.total,Bits.add,Nat.add_mul]; omega

theorem total_more (b w : ℕ) (x : Bits) :
    x.more.total b w = x.total b w+1 := by simp [Bits.total,Bits.more,Nat.add_assoc]

structure Analysis where
  out : Bits
  needed : Bits
  allowed : Bool

private def needed₂ (x y : Analysis) := (x.needed.join y.needed).join (x.out.join y.out)

private def supported : BinaryOp → Bool
  | .add | .mul | .div | .mod | .shiftRight => true
  | _ => false

private def opBound (op : BinaryOp) (x y : Bits) : Bits :=
  match op with
  | .add => (x.join y).more
  | .mul => x.add y
  | _ => x

def analyze {n : ℕ} : Formula n → Analysis
  | .reg _ | .param _ => ⟨{shape:=1},{},true⟩
  | .lit a => ⟨{extra:=a+1},{},true⟩
  | .op o a b =>
    let x := analyze a
    let y := analyze b
    ⟨opBound o x.out y.out,needed₂ x y,x.allowed && y.allowed && supported o⟩
  | .cut a b =>
    let x := analyze a
    let y := analyze b
    ⟨x.out,needed₂ x y,x.allowed && y.allowed⟩
  | .load a =>
    let x := analyze a
    ⟨{word:=1},x.needed.join x.out,x.allowed⟩
  | .select _ a b c d =>
    let x := analyze a
    let y := analyze b
    let u := analyze c
    let v := analyze d
    ⟨u.out.join v.out,(needed₂ x y).join (u.needed.join v.needed),
       x.allowed && y.allowed && u.allowed && v.allowed⟩

private theorem grow {b w v : ℕ} {x y : Bits} (h : v < 2^x.total b w)
    (le : x.total b w ≤ y.total b w) : v<2^y.total b w :=
  h.trans_le (Nat.pow_le_pow_right (by decide) le)

private theorem op_small {b w v z : ℕ} (op : BinaryOp) (x y : Bits) (hs : supported op=true)
    (hv : v<2^x.total b w) (hz : z<2^y.total b w) :
    natOp w op v z < 2^(opBound op x y).total b w := by
  cases op with
  | add =>
    have hv' := grow hv (total_left b w x y)
    have hz' := grow hz (total_right b w x y)
    change v+z < 2^(x.join y).more.total b w
    rw [total_more,Nat.pow_succ]
    omega
  | mul =>
    change v*z<2^(x.add y).total b w
    rw [total_add,Nat.pow_add]
    exact (Nat.mul_le_mul_left _ hz.le).trans_lt
      (Nat.mul_lt_mul_of_pos_right hv (Nat.two_pow_pos _))
  | div => exact (Nat.div_le_self _ _).trans_lt hv
  | mod => exact (Nat.mod_le _ _).trans_lt hv
  | shiftRight =>
    change (if z<w then v>>>z else 0) < 2^x.total b w
    split_ifs
    · exact (Nat.shiftRight_le _ _).trans_lt hv
    · exact Nat.two_pow_pos _
  | sub | bitAnd | bitOr | bitXor | shiftLeft => contradiction

private theorem op_ok {w v z : ℕ} (op : BinaryOp) (hs : supported op=true)
    (hv : v<2^w) (hz : z<2^w) : opFits w op v z := by
  cases op <;> simp_all [supported,opFits]

private theorem widths (b w : ℕ) (x y : Analysis) (h : (needed₂ x y).total b w≤w) :
    x.needed.total b w≤w ∧ y.needed.total b w≤w ∧ x.out.total b w≤w ∧ y.out.total b w≤w := by
  have hl := (total_left b w _ _).trans h
  have hr := (total_right b w _ _).trans h
  exact ⟨(total_left b w _ _).trans hl,(total_right b w _ _).trans hl,
    (total_left b w _ _).trans hr,(total_right b w _ _).trans hr⟩

theorem sound {n b w : ℕ} (f : Formula n) (data : Param → ℕ) (mem : ℕ → ℕ) (v : Fin n → ℕ)
    (hd : ∀ i, data i<2^b) (hm : ∀ i,mem i<2^w) (hv : ∀ i,v i<2^b)
    (ha : (analyze f).allowed=true) (h : (analyze f).needed.total b w≤w) :
    f.Fits w data mem v ∧ f.natural w data mem v<2^(analyze f).out.total b w := by
  induction f with
  | reg i => simpa [analyze,Bits.total,Formula.Fits,Formula.natural] using hv i
  | param i => simpa [analyze,Bits.total,Formula.Fits,Formula.natural] using hd i
  | lit a =>
    refine ⟨trivial,?_⟩
    simpa [analyze,Bits.total,Formula.natural] using (Nat.le_succ a).trans_lt (Nat.lt_two_pow_self (n:=a+1))
  | op op l r il ir =>
    obtain ⟨ad,ao⟩ := Bool.and_eq_true_iff.mp ha
    obtain ⟨al,ar⟩ := Bool.and_eq_true_iff.mp ad
    obtain ⟨hl,hr,wl,wr⟩ := widths b w _ _ h
    obtain ⟨fl,xl⟩ := il al hl
    obtain ⟨fr,xr⟩ := ir ar hr
    exact ⟨⟨fl,fr,op_ok op ao (xl.trans_le (Nat.pow_le_pow_right (by decide) wl))
      (xr.trans_le (Nat.pow_le_pow_right (by decide) wr))⟩,op_small op _ _ ao xl xr⟩
  | cut l r il ir =>
    obtain ⟨al,ar⟩ := Bool.and_eq_true_iff.mp ha
    obtain ⟨hl,hr,wl,wr⟩ := widths b w _ _ h
    obtain ⟨fl,xl⟩ := il al hl
    obtain ⟨fr,xr⟩ := ir ar hr
    exact ⟨⟨fl,fr,xl.trans_le (Nat.pow_le_pow_right (by decide) wl),
      xr.trans_le (Nat.pow_le_pow_right (by decide) wr)⟩,(Nat.sub_le _ _).trans_lt xl⟩
  | load a ih =>
    have ha' := (total_left b w _ _).trans h
    obtain ⟨fa,xa⟩ := ih ha ha'
    refine ⟨⟨fa,xa.trans_le (Nat.pow_le_pow_right (by decide) ((total_right b w _ _).trans h))⟩,?_⟩
    simpa [Formula.natural,analyze,Bits.total] using hm (a.natural w data mem v)
  | select q l r yes no il ir iy ino =>
    have a1 := Bool.and_eq_true_iff.mp ha
    have a2 := Bool.and_eq_true_iff.mp a1.1
    have a3 := Bool.and_eq_true_iff.mp a2.1
    obtain ⟨hl,hr,wl,wr⟩ := widths b w _ _ ((total_left b w _ _).trans h)
    obtain ⟨fl,xl⟩ := il a3.1 hl
    obtain ⟨fr,xr⟩ := ir a3.2 hr
    have hchoices := (total_right b w _ _).trans h
    obtain ⟨fy,xy⟩ := iy a2.2 ((total_left b w _ _).trans hchoices)
    obtain ⟨fnn,xn⟩ := ino a1.2 ((total_right b w _ _).trans hchoices)
    constructor
    · refine ⟨fl,fr,xl.trans_le (Nat.pow_le_pow_right (by decide) wl),
        xr.trans_le (Nat.pow_le_pow_right (by decide) wr),?_⟩
      split <;> assumption
    · dsimp only [Formula.natural]
      split
      · exact grow xy (total_left b w _ _)
      · exact grow xn (total_right b w _ _)

end Estimate
end ThreeFlat.RAM.PhysicalPinsExpr

end OAI
