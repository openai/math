import OAI.Computability.IntegerMultiplication.Packed.Council

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Packed
open Strip Dims Code Loom Port
variable (P G R S : Tape) {A : Type} (K : Type)
abbrev Dome := Pin P × K × Pin G × K × Pin R × K × Pin S
variable {K}
abbrev layouts (k : Series K) :=
  (layout P).cart (k.cart ((layout G).cart (k.cart ((layout R).cart
    (k.cart (layout S))))))

variable {P G R S}
abbrev peek (x : Dome P G R S K) : Triple K :=
  (x.2.1,x.2.2.2.1,x.2.2.2.2.2.1)
abbrev wipe (x : Dome P G R S K) (y : Triple K) : Dome P G R S K :=
  (x.1,y.1,x.2.2.1,y.2.1,x.2.2.2.2.1,y.2.2,x.2.2.2.2.2.2)
abbrev cloud (P G R S : Tape) := Pin P × Pin G × Pin R × Pin S
def flute : Lens (Dome P G R S K) (Triple K) (Pin P × Pin G × Pin R × Pin S) where
  toFun x := (peek x,x.1,x.2.2.1,x.2.2.2.2.1,x.2.2.2.2.2.2)
  invFun x := (x.2.1,x.1.1,x.2.2.1,x.1.2.1,x.2.2.2.1,x.1.2.2,x.2.2.2.2)
  left_inv := fun _=>rfl
  right_inv := fun _=>rfl
def invoke (q : Triple K ≃ Triple K) (P G R S : Tape) : Equiv.Perm (Dome P G R S K) :=
  Optic.field flute q
theorem go (q : Triple K ≃ Triple K) (x : Dome P G R S K) :
    invoke q _ _ _ _ x= wipe x (q (peek x)) := rfl
theorem gone (q : Triple K ≃ Triple K) (x : Dome P G R S K) :
    (invoke q _ _ _ _).symm x= wipe x (q.symm (peek x)) := rfl

inductive Pos
| sun | noon | moon
deriving DecidableEq
instance : Fintype Pos where
  elems := {Pos.sun, Pos.noon, Pos.moon}
  complete x := by cases x <;> simp
open Pos

def note (a : Triple K) : Pos→K
| sun => a.1
| noon => a.2.1
| moon => a.2.2
def mark (f : Pos→K) : Triple K := (f sun, f noon, f moon)

@[simp] theorem noted (f : Pos→K) : note (mark f)=f := by ext (i:Pos) : 1; cases i <;> rfl
@[simp] theorem marked (f : Triple K) : mark (note f)=f := rfl
-- perm: α ≃ α, given n : logical positions ≃ physical so convert physical to logical by note∘n
def arrange (u : Pos ≃ Pos) : Triple K ≃ Triple K where
  toFun x := mark (note x ∘ u)
  invFun x := mark (note x ∘ u.symm)
  left_inv x := by dsimp only; rw [noted]; simp [Function.comp_def]
  right_inv x := by dsimp only; rw [noted]; simp [Function.comp_def]
@[simp] theorem arrange_symm (n : Pos≃Pos) : ((arrange n).symm : Triple K ≃ Triple K)=arrange n.symm := rfl
@[simp] theorem closed (n m : Pos ≃ Pos) :
    ((arrange n).trans (arrange m) : Triple K ≃ Triple K)=arrange (m.trans n) := by
  apply Equiv.ext; intro x
  change mark (note (mark _) ∘ _) = _
  rw [noted]; rfl
theorem invoke_trans (e f : Equiv.Perm (Triple K)) :
    (invoke e P G R S).trans (invoke f P G R S)=invoke (e.trans f) P G R S := rfl -- composition syntactically? peek(wipe x _)=_
theorem invoke_refl : invoke (Equiv.refl (Triple K)) P G R S=Equiv.refl _ := rfl

def agent (q : Pos≃Pos) (p : Equiv.Perm (Triple K)) :=
  ((arrange q).trans p).trans (arrange q).symm
@[simp] theorem agent_con (q : Pos≃Pos) (p r : Equiv.Perm (Triple K)) :
    (agent q p).trans (agent q r)=agent q (p.trans r) := by
  ext x : 1
  simp only [agent,Equiv.trans_apply,Equiv.apply_symm_apply]
theorem agent_id (q : Pos≃Pos) :
    agent q (Equiv.refl (Triple K))=Equiv.refl _ := by
  ext x : 1; simp only [agent,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.refl_apply]
-- after renaming changed physical order.
theorem conjugate (u d : Equiv.Perm Pos) (e : Equiv.Perm (Triple K)) :
    ((arrange d.symm).trans (agent (u.trans d) e)).trans (arrange d)=agent u e := by
  unfold agent
  rw [Equiv.trans_assoc] -- wrong direction
  -- use ext by evaluations, via mark
  apply Equiv.ext; intro x
  simp only [arrange,Equiv.trans_apply,Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk,noted]
  simp [Function.comp_def]

-- alternative spec from function update when target after controls: toFun appears same in controls.
variable {H L i : ℕ} (t : Turn)
noncomputable abbrev placed (x y : Queue H L i) : Equiv.Perm (Queue H L i) := slide (start t x y)
abbrev indexOf (q : Pos) (x : Dome P G R S K) := note (peek x) q
-- logical target location depends on wing
def target (t : Turn) : Pos := bif t.wing then moon else noon
def remote (t : Turn) : Pos := bif t.wing then noon else moon
-- always used when target at moon.
theorem target_end (q : Equiv.Perm Pos) (x : Dome P G R S (Queue H L i)) (e : q (target t)=moon) :
    let y := (invoke (agent q (walk t)) _ _ _ _).symm x
    y=wipe x ((peek x).1,(peek x).2.1,(slide
      (start t (indexOf (q sun) x) (indexOf (q (remote t)) x))).symm (indexOf moon x)) := by
  dsimp only
  rw [gone]
  apply congrArg (wipe x)
  have a : q.symm sun ≠ target t := by intro u; rw [← u] at e; simp at e
  have b : q.symm noon ≠ target t := by intro u; rw [← u] at e; simp at e
  have c : q.symm moon=target t := q.symm_apply_eq.mpr e.symm -- lemma
  let y := peek x
  let v := fun r => note y (q r)
  unfold agent
  simp only [Equiv.symm_trans_apply,Equiv.symm_symm]
  change mark (note ((walk t).symm (mark v)) ∘ ↑q.symm) =
    (note y sun,note y noon, (slide (start t (v sun) (v (remote t)))).symm (note y moon))
  have s : ∀ r,r≠moon → note ((walk t).symm (mark v)) (q.symm r)=note y r := by
    intro r h
    unfold walk
    cases g:t.wing <;>
      have : q.symm r ≠target t := fun z => h (by rw [← q.apply_symm_apply r,z,e])
    all_goals
      cases kh:q.symm r <;> first
       | solve | exfalso; apply this; simp [kh,target,g]
       | have hx : q (q.symm r)=r := by simp
         rw [kh] at hx
         simp [note,mark,v,hx]
  rw [show note y moon=v (target t) by unfold v; rw [e]]
  simp only [mark,Function.comp_apply] at *
  rw [s sun (by decide),s noon (by decide),c]
  cases g:t.wing <;>
    simp [walk,g,note,target,remote]

end Packed

end IntegerMultiplication
end Computability
end OAI
