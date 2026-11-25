import OAI.Hierarchy.DescentCensusScale

namespace OAI
/-! # Sharing intermediate doubles for public census coefficients -/

namespace Hierarchy.DescentCensusRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentSixParty.MarkedCensus
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing

/-- A cheap native row program whose cost depends only on its static
coefficient and primitive reads. It computes its original row expression. -/
structure RowProgram (w : ℕ) (e : Expr) where
  term : ℕ→Term w 0 1
  work : ℕ
  bound : ∀o,(term o).binds≤work
  cheap : ∀o,admissible (term o)
  eval : ∀(o : ℕ) (mem : Memory w) (a : Word w), e.Fits w o → o < 2^w →
    (term o).eval Fin.elim0 mem (fun _=>a)=e.eval mem (a-(o:Word w))

namespace RowProgram
variable {w : ℕ} {e e' x y : Expr}

def plain (w : ℕ) (e : Expr) : RowProgram w e where
  term o := e.compile w o
  work := e.work
  bound _o := (compile_binds ..).le
  cheap o := good_compile e w o
  eval _o m a := eval_compile e m a

def plus (a : RowProgram w e) (b : RowProgram w e') : RowProgram w (.op .add e e') where
  term o := .binary .add (a.term o) (b.term o)
  work := a.work+b.work+1
  bound o := by
    simp only [Term.binary,Term.binds_letThen,Term.binds_rename,Term.binds]
    have := a.bound o;have := b.bound o;omega
  cheap o := by simp [Term.binary,admissible,opAllowed,allowed,a.cheap,b.cheap]
  eval o m j fit word := by rw [Term.eval_binary,a.eval _ _ _ fit.1 word,b.eval _ _ _ fit.2 word];rfl

def ifEq (a : RowProgram w e) (b : RowProgram w e') (yes : RowProgram w x) (no : RowProgram w y) :
    RowProgram w (.branch .eq e e' x y) where
  term o := .select .eq (a.term o) (b.term o) (yes.term o) (no.term o)
  work := a.work+b.work+yes.work+no.work+1
  bound o := by
    simp only [Term.select,Term.binds_letThen,Term.binds_rename,Term.binds]
    have := a.bound o;have := b.bound o;have := yes.bound o;have := no.bound o;omega
  cheap o := by simp [Term.select,admissible,opAllowed,a.cheap,b.cheap,yes.cheap,no.cheap]
  eval o m j fit word := by
    rw [Term.eval_select,a.eval _ _ _ fit.1 word,b.eval _ _ _ fit.2.1 word,yes.eval _ _ _ fit.2.2.1 word,
      no.eval _ _ _ fit.2.2.2 word]
    rfl

/-- The value x is evaluated once. Each subsequent coded digit can reuse
both the original value and the preceding doubled subtotal. -/
def byConstant (c t : ℕ) (fit : c<2^t) (p : RowProgram w e) : RowProgram w (scale c e w) where
  term o := (p.term o).letThen ((ProtocolRAMPortScale.scale w t c).rename (fun _=>0))
  work := p.work+1+2*t
  bound o := by
    rw [Term.binds_letThen,Term.binds_rename]
    have := ProtocolRAMPortScale.binds w t c;have := p.bound o;omega
  cheap o := by simp [p.cheap,DescentWordProduct.scale_ok]
  eval o m j hf room := by
    by_cases zero : w=0
    · have trivialWord (v : Word w) : v.val=0 := by
        have one : 2^w=1:=by rw [zero,pow_zero]
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (v.isLt.trans_eq one))
      exact Fin.ext ((trivialWord _).trans (trivialWord _).symm)
    · have input : e.Fits w o := by
        obtain ⟨t,wt⟩:=Nat.exists_eq_succ_of_ne_zero zero
        rw [wt] at hf ⊢
        exact hf.2.1.1
      simp only [Term.eval_letThen,Term.eval_rename,ProtocolRAMPortScale.eval_scale _ _ _ _ fit,
        Function.comp_apply,Fin.cons_zero,full_scale,p.eval _ _ _ input room]
      exact mul_comm _ _


def times (c : ℕ) (p : RowProgram w e) : RowProgram w (scale c e w) :=
  byConstant c (ProtocolRAMPortScale.bitWidth c) (ProtocolRAMPortScale.fits c) p

def writing (p : RowProgram w e) (out n : ℕ) := PhysicalInputPhases.writing (p.term out) Fin.elim0 out n

theorem writing_exec (p : RowProgram w e) (out n : ℕ) (m : Memory w) (fits : e.Fits w out)
    (room : out+n<2^w) :
    (p.writing out n).Exec m (ProtocolRAM.image out n e m) (4+n*(2*p.work+4)) := by
  let f := fun a : ℕ=>e.eval m ((a:Word w)-(out:Word w))
  have base : (p.writing out n).Spec (·=m) (fun src after=>after=fillSegment out n f src)
      (4+n*(2*(p.term out).binds+4)) :=
    PhysicalInputPhases.writing_spec (p.term out) Fin.elim0 out n room (·=m) f (by
      intro src eq a other _ _ held
      subst src
      rw [p.eval _ _ _ fits (by omega)]
      simpa [f] using eval_below e (a-(out:Word w)) m other fits (fun j hj=>held j (.inl hj)))
  have weak : (p.writing out n).Spec (·=m) (fun src after=>after=fillSegment out n f src)
      (4+n*(2*p.work+4)) :=
    base.mono (fun _ h=>h) (fun _ _ h=>h) (by have :=p.bound out;gcongr)
  intro P R U machine pc reg pub ep prog vals cfg start entry eqn
  subst start
  exact weak machine pc reg pub ep prog vals cfg m entry rfl

end RowProgram
end Hierarchy.DescentCensusRAM

end OAI
