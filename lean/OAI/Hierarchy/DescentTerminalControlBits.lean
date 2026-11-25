import OAI.Hierarchy.DescentTerminalGraphMenu

namespace OAI
/-! # Bit charge of the finite shared terminal scalar key -/

namespace Hierarchy.DescentTerminalControlBits
open DescentKernelHistory DescentTerminalRowBooks DescentTerminalGraphMenu
open scoped BigOperators Classical
noncomputable section

abbrev lg := Nat.clog 2

private theorem alphabet (x : ℕ) : x ≤ 2^(lg x) := Nat.le_pow_clog (by decide) _

private theorem prod {x y a b : ℕ} (hx : x ≤ 2^a) (hy : y ≤ 2^b) : x*y ≤ 2^(a+b) := by
  rw [pow_add]
  exact Nat.mul_le_mul hx hy

private theorem pow {x a n m : ℕ} (hx : x ≤ 2^a) (hn : n ≤ m) : x^n ≤ 2^(m*a) := by
  calc
    x^n ≤ (2^a)^n := Nat.pow_le_pow_left hx n
    _ = 2^(n*a) := by rw [←pow_mul,Nat.mul_comm a n]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hn)

private theorem sigma {n b : ℕ} {X : Fin (n+1)→Type} [∀j,Fintype (X j)]
    (bound : ∀j,Fintype.card (X j) ≤ 2^b) :
    Fintype.card ((j : Fin (n+1)) × X j) ≤ 2^(lg (n+1)+b) := by
  rw [Fintype.card_sigma]
  apply (Finset.sum_le_sum (g:=fun _ : Fin (n+1)=>2^b) fun i _=>bound i).trans
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using
    prod (alphabet (n+1)) (le_rfl : 2^b ≤ 2^b)

def listBits (A M : ℕ) := lg (A+1)+A*lg (M+1)

theorem list_bound (A M : ℕ) : Fintype.card (ShortList A M) ≤ 2^(listBits A M) := by
  apply sigma
  intro j
  simpa only [Fintype.card_fun,Fintype.card_fin] using pow (alphabet (M+1)) (Nat.le_of_lt_succ j.isLt)

def roleBits (tags A U C : ℕ) := lg tags+(listBits A U+listBits A C)
theorem role_bound (tags A U C : ℕ) : Count tags A U C ≤ 2^(roleBits tags A U C) := by
  simpa only [Count,Tag,Fintype.card_prod,Fintype.card_fin,roleBits] using
    prod (alphabet tags) (prod (list_bound A U) (list_bound A C))

def nodeBits (q tagBits H A : ℕ) := tagBits+lg (A+1)+A*lg (q+H+1)+1
def bookBits (q tagBits H N A w : ℕ) :=
  lg (H+1)+(lg (N+1)+(H*lg (w+1)+N*nodeBits q tagBits H A))
def rowBits (q tagBits H N A w V : ℕ) :=
  lg (V+1)+V*bookBits q tagBits H N A w

theorem book_bound {q tags tagBits H N A w : ℕ} (tagRoom : tags ≤ 2^tagBits) :
    Fintype.card (Book q tags H N A w) ≤ 2^(bookBits q tagBits H N A w) := by
  apply sigma
  intro h
  apply sigma
  intro n
  have small := Nat.le_of_lt_succ h.isLt
  have node : 1+tags*(A+1)*(q+h.val+1)^A ≤ 2^(nodeBits q tagBits H A) := by
    have refs : q+h.val+1 ≤ 2^(lg (q+H+1)) := (show _ ≤ q+H+1 by omega).trans (alphabet _)
    have terms := prod (prod tagRoom (alphabet (A+1))) (pow refs (le_rfl : A ≤ A))
    unfold nodeBits
    rw [pow_succ]
    have nz := Nat.two_pow_pos (tagBits+lg (A+1)+A*lg (q+H+1))
    omega
  rw [AddressBook.size]
  exact prod (pow (alphabet (w+1)) small) (pow node (Nat.le_of_lt_succ n.isLt))

theorem row_bound {q tags tagBits H N A w V : ℕ} (tagRoom : tags ≤ 2^tagBits) :
    Fintype.card (Control q tags H N A w V) ≤ 2^(rowBits q tagBits H N A w V) := by
  apply sigma
  intro j
  simpa only [Fintype.card_fun,Fintype.card_fin] using
    pow (book_bound (q:=q) (H:=H) (N:=N) (A:=A) (w:=w) tagRoom) (Nat.le_of_lt_succ j.isLt)

theorem row_key {q tags tagBits H N A w V : ℕ} (tagRoom : tags ≤ 2^tagBits) :
    controlBits q tags H N A w V ≤ rowBits q tagBits H N A w V :=
  Nat.clog_le_of_le_pow (row_bound tagRoom)

/-- Dependence on the longest retained word is logarithmic. Multiplicity
comes only from bounded numbers of operands, atoms and row occurrences. -/
theorem graph_menu_bound {bits q tags A U C H N A0 w V p : ℕ}
    (small : rowBits q (roleBits tags A U C) H N A0 w V+q*p ≤ bits/2) :
    DescentTerminalGraphMenu.Keys q tags A U C H N A0 w V p ≤ 2^(bits/2) := by
  change 2^(controlBits q (Count tags A U C) H N A0 w V)*2^(q*p) ≤ _
  rw [←pow_add]
  exact Nat.pow_le_pow_right (by decide)
    ((Nat.add_le_add_right (row_key (role_bound tags A U C)) _).trans small)

end
end Hierarchy.DescentTerminalControlBits

end OAI
