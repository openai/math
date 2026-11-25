import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalBounded
import OAI.Computability.NearSquareRoot.InterchangeROMProgramEffective
import OAI.Computability.NearSquareRoot.ScheduleGeneratorPhaseLists

/-! # An effective P192 command file for the full repair schedule -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical

open IntegerMultiplication IntegerMultiplication.Code GeneratorSyntax

def leafIndex : Leaf ≃ Fin 9 where
  toFun
    | .duplicate => 0 | .stage => 1 | .extract => 2 | .forward => 3 | .correct => 4
    | .backward => 5 | .restore => 6 | .copyCube => 7 | .finish => 8
  invFun i := match i.val with
    | 0 => .duplicate | 1 => .stage | 2 => .extract | 3 => .forward | 4 => .correct
    | 5 => .backward | 6 => .restore | 7 => .copyCube | _ => .finish
  left_inv a := by cases a <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Primcodable Leaf := Primcodable.ofEquiv (Fin 9) leafIndex

variable {X : Type} [Primcodable X]

theorem effective_steps {n d : X → ℕ} (hn : Computable n) (hd : Computable d) :
    Computable (fun x => steps (n x) (d x)) := by
  let val (p : X → ℕ) (a : Leaf) (hp : Computable p) : Computable (fun x => (p x,a)) :=
    hp.pair (Computable.const _)
  let cons {f : X → List Step} (p : X → ℕ) (a : Leaf) (hp : Computable p) (hf : Computable f) :
      Computable (fun x => (p x,a) :: f x) :=
    Computable.list_cons.comp (val p a hp) hf
  have first := Generator.computable_replicate hd (val n .stage hn)
  have second := Generator.computable_replicate hd (val (fun x => 2*n x) .stage
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) hn))
  have final := Generator.computable_replicate (Primrec.nat_mul.to_comp.comp (Computable.const 2) hd)
    (val (fun x => 3*n x) .stage (Primrec.nat_mul.to_comp.comp (Computable.const 3) hn))
  have checks := cons (fun _ => 0) .extract (Computable.const _)
    (cons n .forward hn (cons n .correct hn (cons n .backward hn (Computable.const [(0,.restore)]))))
  let append {p q : X → List Step} (hp : Computable p) (hq : Computable q) :
      Computable (fun x => p x ++ q x) := Primrec.list_append.to_comp.comp hp hq
  exact append (append (append (append (append (append (Computable.const [(0,Leaf.duplicate)]) first)
    checks) second) (Computable.const [(0,Leaf.copyCube)])) final) (Computable.const [(0,Leaf.finish)])

/-- Uniform code for each of the nine finite leaf families suffices for
the joint dispatch used in quoting a complete command. -/
theorem effective_dispatch {leaf : X → Leaf → Cmd}
    (h : ∀ a, Effective ltr (fun x => leaf x a)) :
    Effective ltr (fun z : X × Leaf => leaf z.1 z.2) := by
  let pick (l : List Leaf) (z : X × Leaf) :=
    l.foldr (fun a rest => if z.2 = a then leaf z.1 a else rest) (leaf z.1 .finish)
  have ht (l : List Leaf) : Effective ltr (pick l) := by
    induction l with
    | nil => exact Computable.comp (f:=fun x => file ltr (leaf x .finish)) (g:=Prod.fst) (h _) Computable.fst
    | cons a l ih =>
      have hb : Computable (fun z : X × Leaf => decide (z.2 = a)) :=
        (Primrec.eq.comp Primrec.snd (Primrec.const a)).decide.to_comp
      have hc : Computable (fun z : X × Leaf => file ltr (leaf z.1 a)) := (h a).comp Computable.fst
      exact (Computable.cond hb hc ih).of_eq (by intro z; by_cases he : z.2=a <;> simp [pick,he])
  apply (ht [.duplicate,.stage,.extract,.forward,.correct,.backward,.restore,.copyCube]).of_eq
  rintro ⟨x,a⟩
  cases a <;> rfl

theorem effective_command {leaf : X → Leaf → Cmd} {ss : X → List Step}
    (h : Effective ltr (fun z : X × Leaf => leaf z.1 z.2)) (hs : Computable ss) :
    Effective ltr (fun x => command (leaf x) (ss x)) := by
  have hk : Computable (fun v : X × Step => v.2.1) := Computable.fst.comp Computable.snd
  have hl : Effective ltr (fun v : X × Step => leaf v.1 v.2.2) :=
    Computable.comp (f:=fun z : X × Leaf => file ltr (leaf z.1 z.2))
      (g:=fun v : X × Step => (v.1,v.2.2)) h (Computable.fst.pair (Computable.snd.comp Computable.snd))
  exact effective_foldr_join ltr hs (InterchangeROM.Parking.effective_parkPrefix hk hl)
    (effective_const ltr .pass)

theorem effective_repair {leaf : X → Leaf → Cmd} {n d : X → ℕ}
    (h : Effective ltr (fun z : X × Leaf => leaf z.1 z.2)) (hn : Computable n) (hd : Computable d) :
    Effective ltr (fun x => command (leaf x) (steps (n x) (d x))) :=
  effective_command h (effective_steps hn hd)

end InterchangeROMRepair.Physical

end NearSquareRoot
end Computability
end OAI
