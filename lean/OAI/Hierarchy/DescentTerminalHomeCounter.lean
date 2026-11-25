import OAI.Hierarchy.DescentTerminalPrivateHome
import OAI.Hierarchy.DescentTerminalMaskedRAM
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.ProtocolRAMEndpointPrefixCheap

namespace OAI
/-! # One chronological private-reference lookup per original common host -/
namespace Hierarchy.DescentTerminalVertexFields.PrivateCounter
open DescentTerminalSiteShelves DescentTerminalRecipeRows ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {q t H N A p groups blocks homes bw : ℕ}
local notation "I" => BlockFields q t H N A p groups blocks
local notation "width" => span q t H N A p
local notation "capacity" => cohortSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) (blocks:=blocks)

structure Banks where
  layout : MaskedShelf blocks
  base : ℕ

variable (C : Banks (blocks:=blocks))
def literal (j : ℕ) : ℕ :=
  if h : j<capacity then privateHome (finPiFinEquiv.symm ⟨j,h⟩ : I) else 0

def menu : Bank := ⟨C.base,groups*blocks*(width+1)⟩

def install (bw : ℕ) : Procedure bw :=
  DescentStaticWordColumn.program bw C.base (literal (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (blocks:=blocks)) capacity

def installed (m : Memory bw) : Memory bw :=
  DescentStaticWordColumn.image C.base (literal (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (blocks:=blocks)) m capacity

local notation "T" => menu (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C
local notation "mount" => installed (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C
local notation "setup" => install (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C

def lookup (table : Bank) : Expr := .lookup table (sumExpr (maskTerm C.layout) (List.finRange (channels blocks)))

structure Shift (L : MaskedShelf blocks) (m : Memory bw) : Prop where
  read : ∀f,∀z:Word bw,(L.weight f).read m z=
    (((z.val%2^(channelSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) f))*
      weightAt (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) f:ℕ):Word bw)

local notation "Shifted" => Shift (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C.layout

structure Room (bw : ℕ) : Prop where
  old : ∀f,(C.layout.channel f).Fits bw C.base ∧ (C.layout.weight f).Fits bw C.base
  space : C.base+capacity<2^bw

local notation "Fits" => Room (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C
local notation "cells" => measured (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups)

theorem count_work (table : Bank) : (lookup C table).work=6+117*blocks := by
  simp only [lookup,Expr.work]
  rw [sum_work (List.finRange (channels blocks)) C.layout]
  simp [channels]
 ; ring

theorem old_read (m : Memory bw) (b : Bank) (fit : b.Fits bw C.base) (z : Word bw) :
    b.read (mount m) z=b.read m z := by
  apply DescentStaticWordColumn.frame _ _ _ _ _ (.inl ?_)
  have limit:=fit.2.2
  have digit:=Nat.mod_lt z.val fit.1
  omega

theorem masked_score (m : Memory bw) (room : Fits bw) (shift : Shifted m) (v : Fin homes) :
    (lookup C T).eval (mount m) (v.val:Word bw)=(privateHome (cells C.layout m v):Word bw) := by
  have inside : ∀f,∀z:Word bw,(C.layout.weight f).read (mount m) z=(C.layout.weight f).read m z :=
    fun f z=>old_read C m _ (room.old f).2 z
  have digits:=mask_index_eval C.layout (mount m) (fun f z=>(inside f z).trans (shift.read f z)) v
  have eqv : cells C.layout (mount m) v=cells C.layout m v := by
    funext f
    unfold measured
    rw [old_read C m (C.layout.channel f) (room.old f).1 (v.val:Word bw)]
  let key : Fin capacity := finPiFinEquiv (cells C.layout m v)
  have keyFit : key.val<2^bw:=key.isLt.trans (by have:=room.space;omega)
  have tableWidth : (T).size=capacity := cohort_size.symm
  change (T).read (mount m) ((sumExpr (maskTerm C.layout) (List.finRange (channels blocks))).eval (mount m) (v.val:Word bw))=_
  rw [digits,eqv]
  change mount m (C.base+(key.val:Word bw).val%(T).size)=_
  rw [Fin.val_cast_of_lt keyFit,tableWidth,Nat.mod_eq_of_lt key.isLt]
  have direct:=DescentStaticWordColumn.read C.base capacity (literal (q:=q) (t:=t) (H:=H) (N:=N)
    (A:=A) (p:=p) (groups:=groups) (blocks:=blocks)) m key.isLt
  refine direct.trans ?_
  unfold literal
  rw [dite_eq_left key.isLt]
  change (privateHome (finPiFinEquiv.symm key : I) : Word bw)=(privateHome (cells C.layout m v):Word bw)
  exact congrArg (fun data : I => (privateHome data : Word bw))
    (finPiFinEquiv.symm_apply_apply (cells C.layout m v))

theorem fits (out : ℕ) (room : Fits bw) (before : C.base+capacity≤out) : (lookup C T).Fits bw out := by
  have size : (T).size=capacity := cohort_size.symm
  have capPos : 0<capacity:=by rw [cohort_size];positivity
  have fit : (T).Fits bw out := by
    refine ⟨?_,?_,?_⟩
    · rw [size]
      exact capPos
    · rw [size]
      have := room.space
      omega
    · rw [size]
      change C.base+capacity≤out
      exact before
  refine ⟨fit,?_⟩
  have one (f : Fin (channels blocks)) : (maskTerm C.layout f).Fits bw out := by
    apply ProtocolRAMGeneratedWrite.fits_mono _ (show C.base≤out by omega)
    exact ⟨(room.old f).2,(room.old f).1,trivial⟩
  generalize List.finRange (channels blocks)=ls
  induction ls with
  | nil=>trivial
  | cons f tail ih=>exact ⟨one f,ih⟩

/-- Native scans write consecutive counts just beyond the extra static
dictionary. Earlier scalar, geometry and operand banks retain their inputs. -/
def program (table : Bank) (bw homes out : ℕ) := (setup bw).seq (scan bw out homes (lookup C table))

def output (table : Bank) (homes out : ℕ) (m : Memory bw) :=
  ProtocolRAM.image out homes (lookup C table) (mount m)

theorem run (m : Memory bw) (room : Fits bw) (out : ℕ) (sep : C.base+capacity≤out) (endAt : out+homes<2^bw) :
    (program (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C T bw homes out).Exec m
      (output (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) C T homes out m)
      ((4+10*capacity)+(4+homes*(16+234*blocks))) := by
  have init:=@DescentStaticWordColumn.mount bw C.base capacity
    (literal (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (blocks:=blocks)) m room.space
  have sweep:=@scan_exec bw out homes (lookup C T) (mount m) (fits C out room sep) endAt
  have tariff : 4+homes*(2*(lookup C T).work+4)=4+homes*(16+234*blocks) := by
    rw [count_work]
    ring
  rw [←tariff]
  exact @Procedure.Exec.then bw (setup bw) (scan bw out homes (lookup C T))
    m (mount m) (ProtocolRAM.image out homes (lookup C T) (mount m)) _ _ (@init) (@sweep)

end
end Hierarchy.DescentTerminalVertexFields.PrivateCounter

end OAI
