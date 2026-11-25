import OAI.ThreeFlat.RAM.TraceTemplateReaders

namespace OAI
/-! # Polynomial native program for all rows of a repeated local gate table -/

namespace ThreeFlat.RAM.TraceTemplate

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr GuardedDescriptor BitLayout Diagonal.TraceAddressRecord
open scoped Fin.CommRing
variable {F : Type*} [CommSemiring F] {w k q t b p : ℕ}

private def names : Inputs (Fin 10) := ⟨0,1,2,3,4,5,6,7,8,9⟩

private def params (N : BitNetwork F q) (code : FieldCode F w) (p b base : ℕ) :
    Fin 10 → Term w k 1 :=
  ![.result 0, .literal (base : Word w), .literal (q : Word w), .literal (N.cells : Word w),
    .literal (N.internal : Word w), .literal 0, .literal (p : Word w), .literal (b : Word w),
    .literal (code.encode 0), .literal (code.encode 1)]

/-- Only the polynomial-size local cell table, address records and fixed
physical dimensions occur as literals in this program. Its sole argument
is the absolute address of a word in the array being generated. -/
def program (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record)
    (p b base : ℕ) : Term w k 1 :=
  bindParams names (callbacks N code R) (params N code p b base)

theorem program_size (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record)
    (p b base : ℕ) : (program (k:=k) N code R p b base).binds ≤ 33*N.cells+42*q+122 := by
  rw [program,binds_bindParams,binds_compile]
  have h := pin_binds (w:=w) (n:=10) (k:=k) R
  simp only [callbacks,copy_binds,Term.literal,Term.binds]
  have hsum : (∑ i : Fin 10, ((params N code p b base i : Term w k 1)).binds) = 9 := by
    simp [Fin.sum_univ_succ,params,Term.binds,Term.literal]
  omega

theorem program_record (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record)
    (input : Fin t → Fin q → BitSource b p) (base : ℕ) (hw : 0<w) (small : 11*N.cells ≤ 2^w)
    (sourceFit : 2+q+N.internal < 2^w) (widthFit : N.cells < 2^w) (eleven : 11 < 2^w)
    (rfit : ∀ (i : Fin t) j, (R j).Fits w i.val)
    (addr : ∀ (i : Fin t) j, (R j).eval i.val = sourceAddress (input i j))
    (words : Fin k → Word w) (mem : Memory w) (i : Fin t) (u : Fin N.cells) (j : Fin 11)
    (fit : recordAddress base N.cells 0 i.val u.val j.val < 2^w) :
    (program N code R p b base).eval words mem
        (fun _ => (recordAddress base N.cells 0 i.val u.val j.val : Word w)) =
      record (Diagonal.GuardedNetwork.network N input empty empty) code (finProdFinEquiv (i,u)) j := by
  let a := recordAddress base N.cells 0 i.val u.val j.val
  let vs := fun ix => (params N code p b base ix).eval words mem (fun _ => (a : Word w))
  have exactParams : names.map vs = recordInputs N code p b 0 base a := by rfl
  have valid := reads N code R input hw small (by omega) rfit addr words mem vs
  have stored := word_record N input empty empty code _ valid base i u j sourceFit widthFit eleven fit
  simp only [program,bindParams,Term.eval_instantiate,eval_compile]
  change word (names.map vs) _ _ _ _ = _
  rw [exactParams]
  exact stored

end ThreeFlat.RAM.TraceTemplate

end OAI
