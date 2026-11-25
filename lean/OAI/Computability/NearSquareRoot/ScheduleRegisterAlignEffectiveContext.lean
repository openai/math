import OAI.Computability.NearSquareRoot.ScheduleRegisterDivide
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyProduct

/-! # Iterated finite syntax contexts in the address-alignment compiler -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterAlign
open IntegerMultiplication Code GeneratorSyntax

/-- Substituting a command in a finite template. The three alternatives of
`inspect` are the two bit leaves and the pair constructor. -/
inductive Template
  | hole
  | fixed (c : Cmd)
  | join (f g : Template)
  | inspect (i : ℕ) (zero one fork : Template)

namespace Template

def subst (c : Cmd) : Template → Cmd
  | .hole => c
  | .fixed d => d
  | .join f g => (subst c f).join (subst c g)
  | .inspect i f g h => splitRoot i (fun b => if b then subst c g else subst c f) (subst c h)

private noncomputable def substituteFile (s : File) : Template → File
  | .hole => s
  | .fixed d => file ltr d
  | .join f g => joinFile (substituteFile s f) (substituteFile s g)
  | .inspect i f g h => lookFile i (Prog.options.map fun x : Option Ltr =>
      joinFile (file ltr (.pop i)) (match x with
        | some (.bit false) => substituteFile s f
        | some (.bit true) => substituteFile s g
        | some .node => substituteFile s h
        | _ => file ltr .pass))

private theorem substituteFile_file (c : Cmd) (f : Template) :
    substituteFile (file ltr c) f = file ltr (subst c f) := by
  induction f with
  | hole | fixed => rfl
  | join f g ih jh => simp only [subst,substituteFile,ih,jh,joinFile_file]
  | inspect i f g h af ag ah =>
    unfold subst splitRoot
    rw [←lookFile_file]
    apply congrArg (lookFile i)
    apply List.map_congr_left
    rintro (_ | (b | _ | _)) _
    all_goals first | cases b <;> simp_all only [joinFile_file, Bool.false_eq_true, ite_false, ite_true] | simp_all only [joinFile_file]

private theorem computable_substituteFile (f : Template) : Computable fun s => substituteFile s f := by
  induction f with
  | hole => exact Computable.id
  | fixed => exact Computable.const _
  | join f g ih jh => exact primrec_joinFile.to_comp.comp ih jh
  | inspect i f g h af ag ah =>
    apply primrec_lookFile.to_comp.comp (Computable.const i)
    apply computable_options_map
    rintro (_ | (b | _ | _)) _
    all_goals apply primrec_joinFile.to_comp.comp (Computable.const _)
    all_goals first | cases b <;> assumption | assumption | exact Computable.const _

def iterate (t : Template) (base : Cmd) : ℕ → Cmd
  | 0 => base
  | n+1 => subst (iterate t base n) t

theorem effective_iterate (t : Template) (base : Cmd) : Effective ltr (iterate t base) := by
  have h := Computable.nat_rec (σ := File) Computable.id (Computable.const (file ltr base))
    ((computable_substituteFile t).comp (Computable.snd.comp Computable.snd)).to₂
  apply h.of_eq
  intro n
  change Nat.rec (file ltr base) (fun _ v => substituteFile v t) n = file ltr (iterate t base n)
  induction n with
  | zero => rfl
  | succ n ih => exact (congrArg (fun s => substituteFile s t) ih).trans (substituteFile_file ..)

/-- Wrapping the hole in a right-component call uses registers zero through two. -/
def right : Template :=
  .inspect 0 (.fixed .pass) (.fixed .pass)
    (.join (.fixed (move 0 1 2)) (.join .hole (.fixed ((move 1 0 2).join (pack 0)))))

theorem subst_right (c : Cmd) : subst c right = KernelEffectiveFamily.rightCmd c := by
  simp [right,subst,KernelEffectiveFamily.rightCmd]

end Template

/-- The arity-dependent division program is emitted by iterating the
two inspections that consume one unary list cell. -/
theorem effective_divide : Effective ltr RegisterDivide.command := by
  let t : Template := .inspect 0 (.fixed (give 0 false)) (.fixed (give 0 false))
    (.inspect 0 .hole .hole (.fixed .pass))
  have e (n : ℕ) : t.iterate RegisterDivide.emit n = RegisterDivide.block n RegisterDivide.emit := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Template.iterate,ih]
      simp [t,Template.subst,RegisterDivide.block]
  have h : Effective ltr (fun n => t.iterate RegisterDivide.emit (n+1)) :=
    (t.effective_iterate RegisterDivide.emit).comp Computable.succ
  exact h.tie.of_eq (fun n => congrArg (file ltr ∘ Prog.tie) (e (n+1)))

end RegisterAlign

end NearSquareRoot
end Computability
end OAI
