import OAI.Computability.VPVNP.PairNativeGeometryArithmetic

/-!
# Native word width and rounded bucket for a live pair

The width is the fourth power of the address width plus ten. The rounded
bucket exponent is computed by integer ceiling division after the power
and ceiling-logarithm instructions have completed.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairNativeGeometry
open BurstRAM PrivateRAM PrimedInputRAM PrimedStackRAM

variable {w : ℕ}

/-- Compute the machine word width by adding ten to the address width in register 5 and raising
the sum to the fourth power in register 6. -/
def widthCode : Code := .seq (literal 11 0 10) (.seq (.line (.binary .add 11 5 11)) (power 6 11 4))

theorem width_run (pub : Fin 11 → Word w) (state : Word w) (m : Memory w) (rs : Regs w 12)
    (r : ℕ) (hr : (rs 5).val = r) (hw : w = (r+10)^4) (h1 : (rs 0).val = 1) :
    ∃ out, Flow.Exec pub state widthCode rs m (List.replicate 17 .tick) out m ∧
      (out 6).val = w ∧ ∀ j : Register, j ≠ 6 → j ≠ 11 → out j = rs j := by
  have hlarge : w < 2^w := Nat.lt_two_pow_self
  have hr10 : r+10 ≤ w := hw ▸ Nat.le_self_pow (by decide) _
  have h10 : 10 < 2^w := by omega
  let s := Function.update rs (11 : Register) (⟨10,h10⟩ : Word w)
  let t := Function.update s (11 : Register) (BinaryOp.add.eval (s 5) (s 11))
  have ha := literal_run pub state m rs 11 0 (by decide) h1 10 h10
  have hb : Flow.Exec pub state (.line (.binary .add 11 5 11)) s m (List.replicate 1 .tick) t m := .line rfl
  have ht : (t 11).val = r+10 := by
    change ((s 5).val+(s 11).val) % (2^w) = r+10
    rw [show (s 5).val = r by simpa [s,Function.update_apply] using hr, show (s 11).val = 10 by simp [s],
      Nat.mod_eq_of_lt (by omega)]
  have hh : (r+10)^4 < 2^w := hw ▸ hlarge
  have hc := power_run pub state m t 6 11 (by decide) (r+10) ht (by omega) 4 hh
  refine ⟨_,seqTicks ha (seqTicks hb hc),by simp [hw],?_⟩
  intro j hj h11
  simp [t,s,Function.update_of_ne hj,Function.update_of_ne h11]

/-- Round the logarithm in register 3 up by ceiling division by positive `b`, then shift one
left by that quotient to obtain the bucket size in register 7. -/
def bucketCode (b : ℕ) : Code :=
  .seq (literal 10 0 (b-1)) (straight (.binary .add 11 3 10)
    [.binary .add 10 10 0, .binary .div 11 11 10, .binary .shiftLeft 7 0 11])

private theorem shifted_value {one x : Word w} (h1 : one.val = 1) (hx : x.val < w) :
    (BinaryOp.shiftLeft.eval one x).val = 2^x.val := by
  have hfit := Nat.pow_lt_pow_right Nat.one_lt_two hx
  simp [BinaryOp.eval,hx,Nat.shiftLeft_eq,h1,Nat.mod_eq_of_lt hfit]

theorem bucket_run (pub : Fin 11 → Word w) (state : Word w) (m : Memory w) (rs : Regs w 12)
    (a b n : ℕ) (hb : 0 < b) (h1 : (rs 0).val = 1) (hlog : (rs 3).val = Nat.clog 2 (n^a))
    (hbfit : b < 2^w) (hsum : Nat.clog 2 (n^a)+(b-1) < 2^w) (hshift : roundedUp a b n < w) :
    ∃ out, Flow.Exec pub state (bucketCode b) rs m (List.replicate (b+4) .tick) out m ∧
      (out 7).val = 2^roundedUp a b n ∧ ∀ j : Register, j ≠ 7 → j ≠ 10 → j ≠ 11 → out j = rs j := by
  let s := Function.update rs (10 : Register) (⟨b-1, by omega⟩ : Word w)
  let num := BinaryOp.add.eval (s 3) (s 10)
  let den := BinaryOp.add.eval (s 10) (s 0)
  let exp := BinaryOp.div.eval num den
  let result := BinaryOp.shiftLeft.eval (s 0) exp
  let out := ([(11,num),(10,den),(11,exp),(7,result)] : List (Register × Word w)).foldl
    (fun x j => Function.update x j.1 j.2) s
  have hlit := literal_run pub state m rs 10 0 (by decide) h1 (b-1) (show b-1 < 2^w by omega)
  have hrest : Flow.Exec pub state
      (straight (.binary .add 11 3 10) [.binary .add 10 10 0,.binary .div 11 11 10,.binary .shiftLeft 7 0 11])
      s m (List.replicate 4 .tick) out m := (Flow.once_sound pub state false _ s m rfl).1
  have ho : (s 0).val = 1 := by simpa [s,Function.update_apply] using h1
  have hx : (s 3).val = Nat.clog 2 (n^a) := by simpa [s,Function.update_apply] using hlog
  have hp : (s 10).val = b-1 := by simp [s]
  have hn : num.val = Nat.clog 2 (n^a)+(b-1) := by
    change ((s 3).val+(s 10).val) % (2^w) = _; rw [hx,hp,Nat.mod_eq_of_lt hsum]
  have hd : den.val = b := by
    change ((s 10).val+(s 0).val) % (2^w) = _; rw [hp,ho,show b-1+1 = b by omega,Nat.mod_eq_of_lt hbfit]
  have he : exp.val = roundedUp a b n := by
    change (num.val / den.val) % (2^w) = roundedUp a b n
    rw [Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt num.isLt),hn,hd,roundedUp,Nat.clog_pow_left]
  refine ⟨out,?_,?_,?_⟩
  · rw [show b+4 = ((b-1)+1)+4 by omega]; exact seqTicks hlit hrest
  · change result.val = _
    rw [shifted_value ho (he ▸ hshift),he]
  · intro j hj h10 h11
    simp [out,s,Function.update_of_ne hj,Function.update_of_ne h10,Function.update_of_ne h11]

end PairNativeGeometry

end VPVNP
end Computability
end OAI
