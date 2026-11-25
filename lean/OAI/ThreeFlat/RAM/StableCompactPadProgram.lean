import OAI.ThreeFlat.RAM.DescriptorExpr
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # Native address translation for three padded pin banks -/

namespace ThreeFlat.RAM.StableCompactPadProgram

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr
open scoped Fin.CommRing

variable {w k : ℕ}

/-- Contract three consecutive banks of width `N` to width `n`. The zero address
supplies the false bit for every pin in the omitted suffix of its bank. -/
def remap (N n a : ℕ) : ℕ :=
  if a < 2+n then a else
  if a < 2+N then 0 else
  if a < 2+N+n then a-(N-n) else
  if a < 2+2*N then 0 else
  if a < 2+2*N+n then a-2*(N-n) else
  if a < 2+3*N then 0 else a-3*(N-n)

theorem remap_constant (N n a : ℕ) (ha : a < 2) : remap N n a = a := by
  simp [remap,show a < 2+n by omega]

theorem remap_pin (N n : ℕ) (s : Fin 3) (v : Fin N) (hn : n ≤ N) :
    remap N n (2+s.val*N+v.val) = if v.val<n then 2+s.val*n+v.val else 0 := by
  have hv := v.isLt
  have banks : s.val = 0 ∨ s.val = 1 ∨ s.val = 2 := by have := s.isLt; omega
  rcases banks with hb | hb | hb <;> rw [hb] <;> unfold remap <;> split_ifs <;> omega

theorem remap_hidden (N n r : ℕ) (hn : n ≤ N) :
    remap N n (2+3*N+r) = 2+3*n+r := by
  unfold remap
  split_ifs <;> omega

private def lessThan (threshold : ℕ) (yes no : Term w k 1) : Term w k 1 :=
  .select .lt (.result 0) (.literal (threshold : Word w)) yes no

private def subtract (d : ℕ) : Term w k 1 :=
  .binary .sub (.result 0) (.literal (d : Word w))

def remapProgram (N n : ℕ) : Term w k 1 :=
  lessThan (2+n) (.result 0) <|
  lessThan (2+N) (.literal 0) <|
  lessThan (2+N+n) (subtract (N-n)) <|
  lessThan (2+2*N) (.literal 0) <|
  lessThan (2+2*N+n) (subtract (2*(N-n))) <|
  lessThan (2+3*N) (.literal 0) (subtract (3*(N-n)))

theorem remapProgram_binds (N n : ℕ) :
    (remapProgram (w:=w) (k:=k) N n).binds = 21 := by
  simp [remapProgram,lessThan,subtract,Term.binary,Term.select,Term.literal,Term.binds]

/-- The only fit checks concern the raw address and the last bank boundary. -/
theorem remapProgram_eval (N n a : ℕ) (hn : n ≤ N) (bankFits : 2+3*N < 2^w)
    (fits : a < 2^w) (words : Fin k → Word w) (mem : Memory w) (vs : Fin 1 → Word w)
    (arg : vs 0 = (a : Word w)) :
    (remapProgram N n).eval words mem vs = (remap N n a : Word w) := by
  have choose (u : ℕ) (hu : u < 2^w) (yes no : Term w k 1) :
      (lessThan u yes no).eval words mem vs =
        if a < u then yes.eval words mem vs else no.eval words mem vs := by
    simp [lessThan,Term.eval_select,Term.eval,Comparison.test,arg,Fin.lt_def,
      Fin.val_cast_of_lt fits,Fin.val_cast_of_lt hu]
  have shifted (d : ℕ) (hd : d ≤ a) :
      (subtract (k:=k) d).eval words mem vs = ((a-d : ℕ) : Word w) := by
    simp [subtract,Term.eval,arg,BinaryOp.eval,Nat.cast_sub hd]
  simp only [remapProgram,remap,choose _ (by omega : 2+n<2^w),
    choose _ (by omega : 2+N<2^w),choose _ (by omega : 2+N+n<2^w),
    choose _ (by omega : 2+2*N<2^w),choose _ (by omega : 2+2*N+n<2^w),
    choose _ bankFits]
  split_ifs <;> first | exact arg | rfl |
    exact shifted _ (by omega)

end ThreeFlat.RAM.StableCompactPadProgram

end OAI
