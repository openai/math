import OAI.Hierarchy.DescentTerminalBinReaddress
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Reading a complete q-slot port row from two adjacent dense rows -/

namespace Hierarchy.DescentTerminalDenseWindow
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization
open scoped BigOperators
noncomputable section

abbrev Format (q p : ℕ) := Fin q→Fin (2*(q*p)+1) × Fin (p+1)
abbrev Menus (q p : ℕ) := Fintype.card (Format q p)
/-- The format code is a mixed-radix integer in physical slot order.
Both directions use only ordinary finite numeric address operations. -/
def formatIndex (q p : ℕ) : Format q p ≃ Fin (Menus q p) :=
  ((Equiv.refl (Fin q)).arrowCongr finProdFinEquiv).trans
    (finFunctionFinEquiv.trans (finCongr (by simp [Menus,Format])))

theorem formatIndex_val {q p : ℕ} (f : Format q p) :
    (formatIndex q p f).val=∑s,(finProdFinEquiv (f s)).val*((2*(q*p)+1)*(p+1))^s.val := rfl

def formatBits (q p : ℕ) := q*(Nat.clog 2 (2*(q*p)+1)+Nat.clog 2 (p+1))

theorem format_room (q p : ℕ) : Menus q p ≤ 2^(formatBits q p) := by
  change Fintype.card (Fin q→Fin (2*(q*p)+1) × Fin (p+1)) ≤ _
  simp only [Fintype.card_fun,Fintype.card_prod,Fintype.card_fin]
  let a:=2*(q*p)+1
  let b:=p+1
  change (a*b)^q ≤ 2^(q*(Nat.clog 2 a+Nat.clog 2 b))
  rw [show q*(Nat.clog 2 a+Nat.clog 2 b)=(Nat.clog 2 a+Nat.clog 2 b)*q from Nat.mul_comm ..,pow_mul,pow_add]
  exact Nat.pow_le_pow_left (Nat.mul_le_mul (Nat.le_pow_clog (by decide : 1<2) _) (Nat.le_pow_clog (by decide : 1<2) _)) q

/-- A dense row occupies just q*p low bits of a physical word; q*p is at
least a constant fraction of the native width in the terminal layout. -/
def dense (B : ℕ) (all : ℕ→Bool) (r : ℕ) : Word B :=
  (wordBits B).symm (fun j=>all (r*B+j.val))

def two {B : ℕ} (a b : Word B) (n : ℕ) : Bool :=
  if h : n<B then wordBits B a ⟨n,h⟩
  else if k : n-B<B then wordBits B b ⟨n-B,k⟩ else false

theorem two_dense {B : ℕ} (all : ℕ→Bool) (r n : ℕ) (h : n<2*B) :
    two (dense B all r) (dense B all (r+1)) n=all (r*B+n) := by
  by_cases atFirst : n<B
  · simp [two,dense,atFirst]
  · have atNext : n-B<B := by omega
    simp only [two,dite_eq_right atFirst,dite_eq_left atNext,dense,Equiv.apply_symm_apply,Nat.succ_mul]
    congr 1
    omega

def select {q p : ℕ} (fmt : Format q p) (lo hi : Word (q*p)) (s : Fin q) (j : Fin p) :=
  if j.val<(fmt s).2.val then two lo hi ((fmt s).1.val+j.val) else false

def word {q p : ℕ} (fmt : Format q p) (lo hi : Word (q*p)) : Word (q*p) :=
  (wordBits _).symm fun z=>select fmt lo hi (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2

theorem word_at {q p : ℕ} (fmt : Format q p) (lo hi : Word (q*p)) (s : Fin q) (j : Fin p) :
    wordBits _ (word fmt lo hi) (finProdFinEquiv (s,j))=select fmt lo hi s j := by
  simp only [word,Equiv.apply_symm_apply,Equiv.symm_apply_apply]

variable {n q p : ℕ} (len : Fin n→ℕ)
def lengthAt (k : ℕ) := if h : k<n then len ⟨k,h⟩ else 0

/-- Exclusive prefix along one genuine neighbor's ordered list of pieces.
Entries after its end are empty. Absolute edge IDs do not enter the key. -/
def pref {n : ℕ} (len : Fin n→ℕ) : ℕ→ℕ
  | 0=>0
  | k+1=>pref len k+lengthAt len k

theorem pref_mono : Monotone (pref len) := monotone_nat_of_le_succ (fun k=>by rw [pref];omega)

theorem delta (small : ∀i,len i ≤ p) (a b : ℕ) : pref len (a+b) ≤ pref len a+b*p := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ,pref,Nat.succ_mul]
    have h : lengthAt len (a+b) ≤ p := by unfold lengthAt;split <;> first | apply small | omega
    omega

/-- Absolute starting bit of the r-th q-slot block of this group. -/
def first (q base r : ℕ) := base+pref len (r*q)
def begin (q base r : ℕ) (s : Fin q) := base+pref len (r*q+s.val)

def format (qp : 0<q*p) (small : ∀i,len i ≤ p) (base r : ℕ) : Format q p := fun s=>
  let u := first len q base r
  let d := begin len q base r s-u
  (⟨u%(q*p)+d,by
    have limit := delta len small (r*q) s.val
    have extra := Nat.mul_le_mul_right p s.isLt.le
    have rem := Nat.mod_lt u qp
    change _<2*(q*p)+1
    dsimp only [d,begin,u,first] at *
    omega⟩,
   ⟨lengthAt len (r*q+s.val),by unfold lengthAt;split <;> first | exact Nat.lt_succ_of_le (small _) | omega⟩)

/-- The compact lookup restores the actual contiguous prefix bits of
each named bundle and zeros its final suffix. The first/last source
words, source offset and partial-bundle cutoffs are all derived here. -/
theorem fetch (qp : 0<q*p) (small : ∀i,len i ≤ p) (base r : ℕ) (all : ℕ→Bool)
    (s : Fin q) (j : Fin p) :
    let nrow := first len q base r/(q*p)
    wordBits _ (word (format len qp small base r) (dense (q*p) all nrow)
      (dense (q*p) all (nrow+1))) (finProdFinEquiv (s,j)) =
      if j.val<lengthAt len (r*q+s.val) then all (begin len q base r s+j.val) else false := by
  intro nrow
  rw [word_at]
  change (if j.val<lengthAt len (r*q+s.val) then
    two (dense (q*p) all nrow) (dense (q*p) all (nrow+1))
      (first len q base r%(q*p)+(begin len q base r s-first len q base r)+j.val)
    else false)=_
  by_cases hj : j.val<lengthAt len (r*q+s.val)
  · simp only [ite_eq_left hj]
    let u := first len q base r
    let t := begin len q base r s
    have mono : u ≤ t := Nat.add_le_add_left (pref_mono len (Nat.le_add_right ..)) base
    have room := delta len small (r*q) (s.val+1)
    rw [Nat.add_succ,pref] at room
    have span : (s.val+1)*p ≤ q*p := Nat.mul_le_mul_right _ s.isLt
    have rem := Nat.mod_lt u qp
    have diag := Nat.div_add_mod u (q*p)
    have lim : u%(q*p)+(t-u)+j.val<2*(q*p) := by
      dsimp only [u,first,t,begin] at *
      omega
    rw [two_dense _ _ _ lim]
    congr 1
    change u/(q*p)*(q*p)+(u%(q*p)+(t-u)+j.val)=t+j.val
    rw [Nat.mul_comm (u/(q*p))]
    omega
  · simp only [ite_eq_right hj]

def entry (bits q p : ℕ) (m : Fin (Menus q p)) (lo hi : Word (q*p)) : Word bits :=
  (wordBits bits).symm (fun j=>if active : j.val<q*p then
    wordBits (q*p) (word ((formatIndex q p).symm m) lo hi) ⟨j.val,active⟩ else false)

theorem entry_bits {bits q p : ℕ} (fits : q*p ≤ bits) (fmt : Format q p) (lo hi : Word (q*p)) (i : Fin (q*p)) :
    wordBits bits (entry bits q p (formatIndex q p fmt) lo hi) (i.castLE fits)=wordBits (q*p) (word fmt lo hi) i := by
  simp [entry,i.isLt]

def rows (bits q p : ℕ) : Vector (Word bits) (Menus q p*(2^(q*p)*2^(q*p))) :=
  Vector.ofFn fun i=>
    let z := finProdFinEquiv.symm i
    let pair := finProdFinEquiv.symm z.2
    entry bits q p z.1 pair.1 pair.2

theorem table_room {bits q p : ℕ} (small : formatBits q p+2*(q*p) ≤ bits/2) :
    Menus q p*(2^(q*p)*2^(q*p)) ≤ 2^(bits/2) := by
  rw [←pow_add]
  apply (Nat.mul_le_mul_right _ (format_room q p)).trans
  rw [←pow_add]
  exact Nat.pow_le_pow_right (by decide) (by omega)

end
end Hierarchy.DescentTerminalDenseWindow

end OAI
