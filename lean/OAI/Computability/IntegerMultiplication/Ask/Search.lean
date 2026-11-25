import OAI.Computability.IntegerMultiplication.Bits.Small
import OAI.Computability.IntegerMultiplication.Code.Iter
import OAI.Computability.IntegerMultiplication.Code.Train

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Ask
open Code Bits Iter
variable {X : Type} [Codec X] (x₀ : X)
abbrev Card (X : Type) := Word × X
abbrev Tab := List (Card X)
def code (x : Word × Word) := !(more x || more x.swap)
@[fun_prop] theorem code_easy : Easy code := by
  unfold code
  apply Easy.compose _ negate
  exact ((easy_more Easy.identity).pair (easy_more Easy.exchange)).compose conn_easy
@[simp] theorem code_true (x y : Word) :
    code (x,y) = true ↔ Bits.value x=Bits.value y := by
  simp only [code,Bool.not_eq_true',Bool.or_eq_false_iff] -- name?
  have h := more_lt x y
  have e := more_lt y x
  cases b : more (x,y) <;> cases v : more (y,x) <;> simp [b,v] at * <;> omega

def foldC (x : Word × Card X) : List X :=
  bif code (x.1,x.2.1) then [x.2.2] else []
@[fun_prop] theorem fold_easy : Easy (foldC (X:=X)) := by
  let u := fun (x:Word × Card X) => (x.1,x.2.1)
  unfold foldC
  have q := Easy.compose (show Easy u from by unfold u; fun_prop) code_easy
  exact (q.pair (Easy.snd (X:=Word) (Y:=Card X))).compose (Easy.ifst (Easy.const ([]:List X))
    (show Easy (fun i:Card X=> [i.2]) from by fun_prop))

def request (w : Word) (t : Tab (X:=X)) :=
  (polyPush foldC (w,t)).flatten
def label (w : Word) (t : Tab (X:=X)) :=
  (request w t).headD x₀
@[fun_prop] theorem poly_label : Poly (fun i:Word × Tab=> label x₀ i.1 i.2) := by
  unfold label request
  exact (Poly.push ([]:Word) (([]:Word),x₀) fold_easy.poly).compose
    (Easy.flatten.compose (leader x₀)).poly
-- precise coverage without layout assumptions
namespace Table
omit [Codec X] in
theorem value (f : ℕ→X) (x : Word) (l : Tab)
    (h : ∀ z∈l, z.2=f (Bits.value z.1))
    (d : ∃ z∈l, Bits.value z.1=Bits.value x) :
    label x₀ x l=f (Bits.value x) := by
  induction l with
  | nil =>
    simp at d
  | cons a l ih =>
    have t := h _ List.mem_cons_self
    have e : label x₀ x (a::l)=(foldC (x,a)++request x l).headD _ := rfl
    rw [e]
    unfold foldC
    by_cases g : Bits.value a.1=Bits.value x
    · rw [(code_true _ _).2 g.symm]; exact t.trans (congrArg f g)
    · rw [show code (x,a.1)=false from Bool.eq_false_iff.mpr (fun h=>g ((code_true _ _).1 h).symm)]
      apply ih (fun z h' => h z (List.mem_cons_of_mem _ h'))
      obtain ⟨z,t,h⟩ := d
      exact ⟨z,(List.mem_cons.mp t).resolve_left (fun d=> g (by rwa [← d])),h⟩
end Table
-- cost theorem for search using known volume budget
variable {I:Type} {p:I→ℝ} {z:I→Tree}
    (t:I→Tab (X:=X)) (w:I→Word)
variable (h : Carries p z (fun i=>send (w i)))
variable (f : Carries p z (fun i=>send (t i)))
include h f
/-- replicated key per table entry; consume O(table + key + table.length*key.length).
Factors table.capacity paid by caller. -/
theorem find (d : ∃ a:ℕ,∀ i,
      ((t i).length+1:ℝ)* (Code.size (w i):ℝ) ≤ (a:ℝ)*p i) :
    Carries p z (fun i=>send (label x₀ (w i) (t i))) := by
  let b := Iter.lineup -- use length cert
  have t0 := f.chain (Carries.func f.budget f.out ruler (Easy.ruler Easy.identity))
  have j := t0.twice h
  obtain ⟨a,d⟩ := d
  let u i := (ruler (t i),w i)
  have v : Carries p z (fun i=> send ((t i).map (fun _=> w i))) := by
    have e := Task.on (Code.generate (X:=Word)) u
    simp only [u,ruler_length,← List.map_const'] at e
    refine j.sequence ⟨f.budget,_,e,a+1,?_⟩
    intro i; specialize d i
    push_cast at d ⊢
    linarith [f.budget i]
  let y := fun i=> ((t i).map (fun _=> w i),t i)
  have x := v.twice f
  have A := x.chain (Carries.func (y:=y) f.budget x.out
    (fun (p:List Word × Tab)=> ((lock foldC [] ([],x₀) p).flatten).headD x₀)
    (((Code.easy_lock foldC fold_easy [] ([],x₀)).compose Easy.flatten).compose (leader _)))
  suffices e : ∀i:I,
      lock foldC ([]:Word) (([]:Word),x₀) (y i) = polyPush foldC (w i,t i) by
    simpa only [e,label,request] using A
  intro i
  have f := IntegerMultiplication.Code.fair (fun _=>w i) id (t i) ([]:Word) (([]: Word),x₀)
  simp only [List.map_id] at f
  unfold lock y
  rw [f,List.map_map]
  rfl
end Ask

end IntegerMultiplication
end Computability
end OAI
