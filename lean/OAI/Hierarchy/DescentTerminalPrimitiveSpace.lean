import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace OAI
/-! # Exact address space of the six new primitive fields on the terminal host -/
namespace Hierarchy.DescentTerminalPrimitiveArena
def pad (n:ℕ):=2^Nat.clog 2 n
theorem covered (n:ℕ):n≤pad n:=Nat.le_pow_clog (by decide) n
theorem pad_le (n:ℕ):pad n≤2*n+1:=by
  by_cases small:n≤1
  · interval_cases n <;> decide
  · have pos:=Nat.clog_pos (by decide : 1<2) (by omega:1<n)
    have prior:=Nat.pow_pred_clog_lt_self (by decide : 1<2) (by omega:1<n)
    cases eqn:Nat.clog 2 n with
    | zero=>omega
    | succ e=>simp only [eqn,Nat.pred_succ] at prior;unfold pad;rw [eqn,pow_succ];omega
structure Shape where
  blocks:ℕ
  shops:ℕ
  columns:ℕ
  pointerBits:ℕ
  countBits:ℕ
def fee (L d:ℕ):=L*2^d+2^(d*L)
namespace Shape
def rows (s:Shape):=s.blocks*s.shops
def guard (s:Shape):=pad s.rows+pad s.shops
def gather (s:Shape) (start:ℕ):=start+s.rows+s.rows+s.guard
def rom (s:Shape) (start:ℕ):=s.gather start+s.columns*s.rows+pad s.rows
def «public» (s:Shape) (start:ℕ):=s.rom start+fee s.columns s.pointerBits
def pointers (s:Shape) (start:ℕ):=s.«public» start+s.rows+fee s.columns s.pointerBits
def counting (s:Shape) (start:ℕ):=s.pointers start+s.rows+s.guard
def number (s:Shape) (start:ℕ):=s.counting start+fee 3 s.countBits
def widths (s:Shape) (start:ℕ):=s.number start+s.rows+s.guard
def finish (s:Shape) (start:ℕ):=s.widths start+s.rows+s.guard

theorem exact_end (s:Shape) (start:ℕ):
    s.finish start=start+(s.columns+6)*s.rows+5*pad s.rows+4*pad s.shops+
      2*fee s.columns s.pointerBits+fee 3 s.countBits:=by
  unfold finish widths number counting pointers «public» rom gather guard;ring

theorem end_le (s:Shape) (start:ℕ):
    s.finish start≤start+(s.columns+16)*s.rows+8*s.shops+9+2*fee s.columns s.pointerBits+fee 3 s.countBits:=by
  rw [exact_end];have a:=pad_le s.rows;have b:=pad_le s.shops;simp only [Nat.add_mul];omega

end Shape

theorem fee_le (L d h:ℕ) (pos:0<L) (bits:d*L+Nat.clog 2 (L+1)≤h):
    fee L d≤2^h:=by
  have exponent:d≤d*L:=by simpa using Nat.mul_le_mul_left d pos
  have powers:2^d≤2^(d*L):=Nat.pow_le_pow_right (by decide) exponent
  calc
    fee L d≤(L+1)*2^(d*L):=by unfold fee;rw [Nat.add_mul,Nat.one_mul];exact Nat.add_le_add_right (Nat.mul_le_mul_left L powers) _
    _≤2^(Nat.clog 2 (L+1))*2^(d*L):=Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _)
    _≤2^h:=by rw [←pow_add];exact Nat.pow_le_pow_right (by decide) (by omega)

/-- When both lookup alphabets fit the half-word cap, the remaining end is
linear in the genuine position, gather and outer-host row counts. -/
theorem priced (s:Shape) (start h:ℕ) (positive:0<s.columns)
    (pointer:s.pointerBits*s.columns+Nat.clog 2 (s.columns+1)≤h/2)
    (count:3*s.countBits+2≤h/2) :
    s.finish start≤start+(s.columns+16)*s.rows+8*s.shops+9+3*2^(h/2) := by
  have a:=fee_le s.columns s.pointerBits (h/2) positive pointer
  have lc:Nat.clog 2 (3+1)=2:=by decide
  have b:=fee_le 3 s.countBits (h/2) (by decide) (by rw [lc];omega)
  have c:=s.end_le start
  omega

end Hierarchy.DescentTerminalPrimitiveArena

end OAI
