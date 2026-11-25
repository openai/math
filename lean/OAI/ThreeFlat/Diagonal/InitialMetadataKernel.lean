import Mathlib.Tactic.FinCases
import OAI.ThreeFlat.Diagonal.NavigationArchive

namespace OAI
/-! # Evaluation of the native five-word kernel and two-word half-header at every initial site -/

namespace ThreeFlat.Diagonal.NavigationPass.Archive
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan RAM.PhysicalPinsExpr
open scoped Fin.CommRing

variable {W : ℕ}

private abbrev V (m : Memory W) (a : ℕ) (f : Formula 1) :=
  f.natural W (fun _ => 0) (fun j => (m j).val) (fun _ => a)
private abbrev Good (m : Memory W) (a : ℕ) (f : Formula 1) :=
  f.Fits W (fun _ => 0) (fun j => (m j).val) (fun _ => a)

private theorem word_value (m : Memory W) (a : ℕ) (f : Formula 1) (h : Good m a f) :
    f.value (fun _ => 0) m (fun _ => (a : Word W))=(V m a f : Word W) := by
  simpa only [Nat.cast_zero,Fin.cast_val_eq_self] using
    (Formula.value_eq_natural f (fun _ => 0) (fun j => (m j).val) (fun _ => a) h)

private theorem choose {m : Memory W} {a : ℕ} {x y u v : Formula 1}
    (hx : Good m a x) (hy : Good m a y) (lx : V m a x<2^W) (ly : V m a y<2^W)
    (yes : Good m a u) (no : Good m a v) : Good m a (eqz x y u v) := by
  refine ⟨hx,hy,lx,ly,?_⟩
  split <;> assumption

variable (A : Archive) (m : Memory W) (H : Scans.Header (A.control:Word W) m A.seed 63 A.seedWords)
    (controlRoom : A.control<2^W)

include H controlRoom in
private theorem pointer : (m A.control).val=A.seed := by
  simpa only [Fin.val_cast_of_lt controlRoom] using H.pointer

include H controlRoom in
private theorem readField (a i : ℕ) (hi : i≤63) : V m a (A.initialField i)=A.seedWords i := by
  change (m ((m A.control).val+i)).val=_
  rw [pointer A m H controlRoom]
  exact H.values _ hi

include H controlRoom in
private theorem goodField (a i : ℕ) (hi : i≤63) : Good m a (A.initialField i) := by
  refine ⟨⟨⟨trivial,controlRoom⟩,trivial,trivial⟩,?_⟩
  change (m A.control).val+i<2^W
  rw [pointer A m H controlRoom]
  have := H.fit
  omega

include H controlRoom in
private theorem ordinal {i t : ℕ} (hi : i≤63) (wide : t<2^W) (row j : ℕ) (hj : j<t)
    (room : A.seedWords i+(row*t+j)<2^W) :
    let a:=A.seedWords i+(row*t+j)
    let pos:=A.initialOffset i
    Good m a (div pos (L t)) ∧ Good m a (rem pos (L t)) ∧
      V m a (div pos (L t))=row ∧ V m a (rem pos (L t))=j := by
  let a:=A.seedWords i+(row*t+j)
  let pos:=A.initialOffset i
  have get:=readField A m H controlRoom a i hi
  have ind : V m a pos=row*t+j := by
    change a-V m a (A.initialField i)=_
    rw [get]; exact Nat.add_sub_cancel_left ..
  have fieldFit : V m a (A.initialField i)<2^W := by
    rw [get]
    exact (Nat.le_add_right (A.seedWords i) (row*t+j)).trans_lt room
  have fc : Good m a pos :=
    ⟨trivial,goodField A m H controlRoom a i hi,room,fieldFit⟩
  have fits : V m a pos<2^W := by rw [ind];omega
  refine ⟨⟨fc,trivial,fits,wide⟩,⟨fc,trivial,fits,wide⟩,?_,?_⟩
  · change V m a pos/t=row
    rw [ind,Nat.add_comm,Nat.mul_comm row t,Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt hj,Nat.zero_add]
  · change V m a pos%t=j
    rw [ind,Nat.add_comm,Nat.mul_comm row t,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hj]

private theorem offset_lt {sites k : ℕ} (row : Fin sites) (col : Fin k) : row.val*k+col.val<k*sites := by
  have cmp := Nat.mul_le_mul_right k row.isLt
  rw [Nat.succ_mul] at cmp
  have bound := col.isLt
  rw [Nat.mul_comm k sites]
  omega

include H controlRoom in
theorem initialKernel_word
    (recordRoom : A.initialRecords+(7+8*A.initialDegree)*A.initialSites<2^W) (wide : 8<2^W)
    (row : Fin A.initialSites) (col : Fin 5) :
    A.initialKernel.value (fun _=>0) m (fun _ : Fin 1=>((A.seedWords 7+(row.val*5+col.val):ℕ):Word W)) =
      ((![A.seed,row.val,0,row.val%A.remainingLanes,row.val/A.remainingLanes] : Fin 5→ℕ) col : Word W) := by
  let a:=A.seedWords 7+(row.val*5+col.val)
  let r := div (A.initialOffset 7) (L 5)
  let c := rem (A.initialOffset 7) (L 5)
  have bound := offset_lt row col
  have room : a<2^W := by
    change A.initialRecords+(row.val*5+col.val)<2^W
    rw [Nat.add_mul] at recordRoom
    omega
  have h5 : 5<2^W := by omega
  obtain ⟨fr,fc,rv,cv⟩ := ordinal A m H controlRoom (i:=7) (by decide) h5 row.val col.val col.isLt room
  change Good m a r at fr
  change Good m a c at fc
  change V m a r=row.val at rv
  change V m a c=col.val at cv
  have idx : row.val*5+col.val<2^W := (Nat.le_add_left _ (A.seedWords 7)).trans_lt room
  have rs : V m a r<2^W := by rw [rv];omega
  have cs : V m a c<2^W := by rw [cv]; exact col.isLt.trans h5
  have pl : V m a (A.initialField 6)=A.remainingLanes := readField A m H controlRoom a 6 (by decide)
  have fl := goodField A m H controlRoom a 6 (by decide)
  have ls : V m a (A.initialField 6)<2^W := (m ((m A.control).val+6)).isLt
  have test (i : ℕ) (small : i<2^W) {u v : Formula 1} (hu : Good m a u) (hv : Good m a v) :
      Good m a (eqz c (L i) u v) := choose fc trivial cs small hu hv
  have fit : Good m a A.initialKernel := test 0 (by omega) ⟨trivial,controlRoom⟩
    (test 1 (by omega) fr (test 2 (by omega) trivial
      (test 3 (by omega) ⟨fr,fl,rs,ls⟩ ⟨fr,fl,rs,ls⟩)))
  rw [word_value _ _ _ fit]
  apply congrArg (fun n : ℕ => (n : Word W))
  change (if decide (V m a c=0) then (m A.control).val else if decide (V m a c=1) then V m a r
    else if decide (V m a c=2) then 0 else if decide (V m a c=3) then V m a r%V m a (A.initialField 6)
    else V m a r/V m a (A.initialField 6))=_
  rw [pointer A m H controlRoom,rv,cv,pl]
  fin_cases col <;> rfl

include H controlRoom in
theorem initialHalfHeader_word
    (recordRoom : A.initialRecords+(7+8*A.initialDegree)*A.initialSites<2^W) (wide : 8<2^W)
    (row : Fin A.initialSites) (col : Fin 2) :
    A.initialHalfHeader.value (fun _=>0) m (fun _ : Fin 1=>((A.seedWords 9+(row.val*2+col.val):ℕ):Word W)) =
      ((![2*A.initialDegree,A.seedWords 11+8*A.initialDegree*row.val] : Fin 2→ℕ) col : Word W) := by
  let a:=A.seedWords 9+(row.val*2+col.val)
  let r:=div (A.initialOffset 9) (L 2)
  let c:=rem (A.initialOffset 9) (L 2)
  have bound:=offset_lt row col
  have room : a<2^W := by
    change A.initialRecords+5*A.initialSites+(row.val*2+col.val)<2^W
    rw [Nat.add_mul] at recordRoom
    omega
  have h2 : 2<2^W := by omega
  obtain ⟨fr,fc,rv,cv⟩ := ordinal A m H controlRoom (i:=9) (by decide) h2 row.val col.val col.isLt room
  change Good m a r at fr
  change Good m a c at fc
  change V m a r=row.val at rv
  change V m a c=col.val at cv
  have cs : V m a c<2^W := by rw [cv]; exact col.isLt.trans h2
  have b := readField A m H controlRoom a 11 (by decide)
  have fit : Good m a A.initialHalfHeader :=
    choose fc trivial cs (show 0<2^W by omega) trivial
      ⟨goodField A m H controlRoom a 11 (by decide),⟨fr,trivial,trivial⟩,trivial⟩
  rw [word_value _ _ _ fit]
  apply congrArg (fun n : ℕ => (n : Word W))
  change (if decide (V m a c=0) then 2*A.initialDegree else
    V m a (A.initialField 11)+V m a r*(8*A.initialDegree))=_
  rw [cv,rv,b,Nat.mul_comm row.val (8*A.initialDegree)]
  fin_cases col <;> rfl


end ThreeFlat.Diagonal.NavigationPass.Archive

end OAI
