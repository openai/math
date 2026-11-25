import OAI.ThreeFlat.RAM.TraceRawLookup
import OAI.ThreeFlat.RAM.PhysicalInputPhases

namespace OAI
/-! # Installing the fixed native H row-reader arguments -/
namespace ThreeFlat.RAM.TraceRawLookup
open Computability.VPVNP.BurstRAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing
variable {W : ℕ}

private def lookup (W base : ℕ) : List (Fin FixedTraceProgram.P)→Term W FixedTraceProgram.P 1
  | []=>.literal 0
  | j::js=>.select .eq (.result 0) (.literal (base+j.val:ℕ)) (.parameter j) (lookup W base js)

private theorem lookup_size (base : ℕ) (js : List (Fin FixedTraceProgram.P)) :
    (lookup W base js).binds=3*js.length+1 := by
  induction js with
  | nil=>rfl
  | cons j js ih=>
    simp only [lookup,Term.select,Term.literal,Term.parameter,Term.binds_letThen,Term.binds_rename,Term.binds,
      List.length_cons,ih]
    omega

private theorem lookup_at (v : Fin FixedTraceProgram.P→Word W) (m : Memory W)
    (base : ℕ) (fit : base+FixedTraceProgram.P≤2^W) (i : Fin FixedTraceProgram.P)
    (js : List (Fin FixedTraceProgram.P)) (hi : i∈js) :
    (lookup W base js).eval v m (fun _=>(base+i.val:ℕ))=v i := by
  induction js with
  | nil=>simp at hi
  | cons j js ih=>
    have iFit : base+i.val<2^W:=by have:=i.isLt;omega
    have jFit : base+j.val<2^W:=by have:=j.isLt;omega
    by_cases eq : i=j
    · subst j
      simp [lookup,Comparison.test,Term.eval]
    · have neq : ((base+i.val:ℕ):Word W)≠((base+j.val:ℕ):Word W):=by
        intro same
        have a:=congrArg Fin.val same
        rw [Fin.val_cast_of_lt iFit,Fin.val_cast_of_lt jFit] at a
        exact eq (Fin.ext (by omega))
      have rest:=ih (List.mem_cons.mp hi |>.resolve_left eq)
      simpa only [lookup,Term.eval_select,Term.eval,Term.eval_literal,Term.eval_parameter,Comparison.test,
        beq_iff_eq,ite_eq_right neq] using rest

private def headerValue (R : Layout) (v : Fin FixedTraceProgram.P→Word W) (z : ℕ) : Word W :=
  if h:z-R.publicBase<FixedTraceProgram.P then v ⟨_,h⟩ else 0

def install (R : Layout) (v : Fin FixedTraceProgram.P→Word W) : Procedure W :=
  PhysicalInputPhases.writing (lookup W R.publicBase (List.finRange _)) v R.publicBase FixedTraceProgram.P

def installed (R : Layout) (v : Fin FixedTraceProgram.P→Word W) (m : Memory W) :=
  fillSegment R.publicBase FixedTraceProgram.P (headerValue R v) m

theorem install_spec (R : Layout) (v : Fin FixedTraceProgram.P→Word W)
    (fit : R.publicBase+FixedTraceProgram.P<2^W) :
    (install R v).Spec (fun _=>True) (fun m out=>out=installed R v m)
      (4+FixedTraceProgram.P*(2*(3*FixedTraceProgram.P+1)+4)) := by
  have cost : (lookup W R.publicBase (List.finRange FixedTraceProgram.P)).binds =
      3*FixedTraceProgram.P+1 := by rw [lookup_size,List.length_finRange]
  rw [←cost]
  intro P registers slots machine
  exact PhysicalInputPhases.writing_spec (lookup W R.publicBase (List.finRange _)) v
    R.publicBase FixedTraceProgram.P fit (fun _=>True) (headerValue R v) (by
      intro m _ a s lo hi _
      let j:Fin FixedTraceProgram.P:=⟨a.val-R.publicBase,by omega⟩
      have addr : ((R.publicBase+j.val:ℕ):Word W)=a:=by
        have e:R.publicBase+j.val=a.val:=by dsimp [j];omega
        rw [e,Fin.cast_val_eq_self]
      have q:=lookup_at v s R.publicBase fit.le j (List.finRange _) (List.mem_finRange j)
      rw [addr] at q
      simpa [headerValue,show a.val-R.publicBase<FixedTraceProgram.P by omega,j] using q) machine

theorem installed_words (R : Layout) (v : Fin FixedTraceProgram.P→Word W) (m : Memory W) :
    words R (installed R v m)=v := by
  funext j
  simp [words,installed,fillSegment,headerValue,j.isLt]

theorem installed_outside (R : Layout) (v : Fin FixedTraceProgram.P→Word W) (m : Memory W) {z : ℕ}
    (h : z<R.publicBase ∨ R.publicBase+FixedTraceProgram.P≤z) : installed R v m z=m z := by
  simp [installed,fillSegment,show ¬(R.publicBase≤z ∧ z<R.publicBase+FixedTraceProgram.P) by omega]

theorem installed_resources (R : Layout) (v : Fin FixedTraceProgram.P→Word W) :
    (install R v).labels+(install R v).registers+(install R v).slots≤300 := by
  simp [install,PhysicalInputPhases.writing,Term.labels_eq,lookup_size,FixedTraceProgram.P]


end ThreeFlat.RAM.TraceRawLookup

end OAI
