import Mathlib.Data.List.FinRange
import Mathlib.Tactic

namespace OAI
/-! # Consecutive word sites under edge relabeling and reversal -/

namespace Hierarchy.WireTelescope.VisitOrder
open scoped Classical

variable {V U E D : Type*}

def Between (edge : V × V) (a b : V) : Prop :=
  (edge.1=a ∧ edge.2=b) ∨ (edge.2=a ∧ edge.1=b)

theorem Between.swap {edge : V×V} {a b : V} (h : Between edge a b) : Between edge b a := by
  rcases h with ⟨ha,hb⟩|⟨ha,hb⟩
  · exact Or.inr ⟨hb,ha⟩
  · exact Or.inl ⟨hb,ha⟩

theorem Between.map {e : V×V} {f : U×U} {a b : V} (place : V→U)
    (inc : Between f (place e.1) (place e.2)) (h : Between e a b) :
    Between f (place a) (place b) := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact inc
  · exact inc.swap

/-- Occurrence `j` joins the two public visit boundaries `start+j` and
`start+j+1`. The definition is insensitive to the physical row orientation. -/
def Steps (ends : E → V×V) (v : ℕ→V) (start : ℕ) (es : List E) : Prop :=
  ∀ j (hj : j<es.length), Between (ends es[j]) (v (start+j)) (v (start+j+1))

theorem Steps.append {ends : E→V×V} {v : ℕ→V} {a : ℕ} {xs ys : List E}
    (left : Steps ends v a xs) (right : Steps ends v (a+xs.length) ys) :
    Steps ends v a (xs++ys) := by
  intro j hj
  by_cases h : j<xs.length
  · simpa only [List.getElem_append_left h] using left j h
  · have hr : j-xs.length<ys.length := by simp only [List.length_append] at hj;omega
    rw [List.getElem_append_right (by omega : xs.length≤j)]
    have step := right (j-xs.length) hr
    rwa [show a+xs.length+(j-xs.length)=a+j by omega] at step

theorem Steps.map {ends : E→V×V} {out : D→U×U} {v : ℕ→V} {xs : List E}
    (h : Steps ends v 0 xs) (place : V→U) (emit : E→D)
    (keeps : ∀e, Between (out (emit e)) (place (ends e).1) (place (ends e).2)) :
    Steps out (place ∘ v) 0 (xs.map emit) := by
  intro j hj
  have ok : j<xs.length := by simpa using hj
  simpa [Function.comp_def] using Between.map place (keeps xs[j]) (h j ok)

theorem Steps.reverse {ends : E→V×V} {v : ℕ→V} {xs : List E} (h : Steps ends v 0 xs) :
    Steps ends (fun j=>v (xs.length-j)) 0 xs.reverse := by
  intro j hj
  have lt : j<xs.length := by simpa using hj
  rw [List.getElem_reverse]
  have step := (h (xs.length-1-j) (by omega)).swap
  simpa only [Nat.zero_add,show xs.length-1-j+1=xs.length-j by omega,
    show xs.length-1-j=xs.length-(j+1) by omega,
    show xs.length-(j+1)+1=xs.length-j by omega] using step

end Hierarchy.WireTelescope.VisitOrder

end OAI
