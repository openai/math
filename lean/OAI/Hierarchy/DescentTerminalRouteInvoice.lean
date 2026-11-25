import OAI.Hierarchy.DescentTerminalBookInvoice

namespace OAI
/-! # Packed emitter update and final decode over every terminal bin -/
namespace Hierarchy.DescentTerminalLocalPortBook.Book
open DescentDyadicSpan DescentTerminalRouteRows DescentTerminalRouteLedger
noncomputable section

def routeBits (V A W q : ℕ) := rowBits q (Nat.clog 2 (W*2^(nameBits 4 (V*A))))

/-- Padded fixed lookup tables for local books and the three code-indexed
terminal routing columns. The two further columns indexed by the whole
terminal arm have lengths `pool` and `3*pool`. -/
def fixedWords (V A W q : ℕ) :=
  let c:=routeBits V A W q
  lookupWords V A W+span (2^c)+span (radix W c)+span (2^(W*c))

theorem lookup_le_fixed (V A W q : ℕ) : lookupWords V A W≤fixedWords V A W q := by
  dsimp only [fixedWords]
  omega

theorem fixed_envelope (V A W q n : ℕ) (node : V≤n) (incidence : V*A≤n)
    (operand : A≤n) (width : W≤n) (bin : q≤n) (positive : 0<n) :
    fixedWords V A W q ≤ 2^(256*(n*n*n)) := by
  let bits:=nameBits 4 (V*A)
  let c:=routeBits V A W q
  have b : bits≤5*n := Nat.clog_le_of_le_pow <|
    (show 4*(V*A)+1≤5*n by omega).trans (Nat.lt_two_pow_self.le)
  have addr : Nat.clog 2 (W*2^bits)≤6*n := by
    apply Nat.clog_le_of_le_pow
    calc
      W*2^bits ≤ 2^W*2^bits := Nat.mul_le_mul_right _ (Nat.lt_two_pow_self.le)
      _ = 2^(W+bits) := (pow_add ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have sq : n≤n*n:=Nat.le_mul_of_pos_right _ positive
  have cube : n*n≤n*n*n:=Nat.le_mul_of_pos_right _ positive
  have size : c≤14*(n*n) := by
    change 2*(q*(Nat.clog 2 (W*2^bits)+1))≤_
    have low:=Nat.mul_le_mul bin (Nat.succ_le_succ addr)
    nlinarith
  have joined : W*c≤14*(n*n*n) := by
    calc
      _ ≤ n*(14*(n*n)) := Nat.mul_le_mul width size
      _ = _ := by ring
  let cap:=2^(128*(n*n*n))
  have codes : 2^c≤ cap := Nat.pow_le_pow_right (by decide) (by omega)
  have states : 2^(W*c)≤ cap := Nat.pow_le_pow_right (by decide) (by omega)
  have table : radix W c≤ cap := calc
    W*(2^c*2^(W*c)) ≤ 2^W*(2^c*2^(W*c)) := Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    _ = 2^(W+(c+W*c)) := by rw [pow_add,pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have books : lookupWords V A W≤ cap := (lookup_envelope V A W n node incidence operand width positive).trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ cube))
  have bound : fixedWords V A W q≤16*cap := by
    have one:=span_le (2^c)
    have two:=span_le (radix W c)
    have three:=span_le (2^(W*c))
    have good : 0< cap:=Nat.two_pow_pos _
    change lookupWords V A W+span (2^c)+span (radix W c)+span (2^(W*c))≤16*cap
    omega
  exact bound.trans (show 2^4*2^(128*(n*n*n))≤_ by
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by nlinarith [Nat.mul_pos (Nat.mul_pos positive positive) positive]))

end
end Hierarchy.DescentTerminalLocalPortBook.Book

end OAI
