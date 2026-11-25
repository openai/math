import OAI.Hierarchy.DescentDistinctRAM
import OAI.Hierarchy.DescentLivePrivateWords

namespace OAI
/-! # The observed terminal counter counts precisely the occupied local hidden variables -/

namespace Hierarchy.DescentTerminalPrivateCount
open DescentKernelHistory DescentDistinctRAM DescentDistinctWindow
open scoped Classical BigOperators
noncomputable section
variable {V Tag : Type} [Fintype V] {B : V→Type} (r : (v : V)→Recipe Tag (B v))
abbrev Slots := Σv,Σu : (r v).Node,Fin ((r v).arity u)
abbrev Names := Σv,(r v).UsedWord

def label (x : Slots r) : Option (Names r) :=
  match h : (r x.1).operand x.2.1 x.2.2 with
  | .inl _=>none
  | .inr j=>some ⟨x.1,⟨j,x.2.1,x.2.2,h⟩⟩

def tags {n : ℕ} (slot : Slots r↪Fin n) (i : Fin n) : Option (Names r) :=
  if h : ∃x,slot x=i then label r h.choose else none

theorem tag_read {n : ℕ} (slot : Slots r↪Fin n) (x : Slots r) :
    tags r slot (slot x)=label r x := by
  have ok : ∃y,slot y=slot x := ⟨x,rfl⟩
  rw [tags,dite_eq_left ok,slot.injective ok.choose_spec]

theorem every_label {n : ℕ} (slot : Slots r↪Fin n) (a : Names r) :
    Occupied (tags r slot) a := by
  rcases a with ⟨v,⟨t,⟨u,j,h⟩⟩⟩
  refine ⟨slot ⟨v,u,j⟩,?_⟩
  rw [tag_read]
  unfold label
  split
  · rename_i b e
    cases e.symm.trans h
  · rename_i k e
    have same : k=t := Sum.inr.inj (e.symm.trans h)
    subst k
    rfl

theorem uses_total {n : ℕ} (slot : Slots r↪Fin n) :
    Fintype.card {a //Occupied (tags r slot) a}=∑v,Fintype.card (r v).UsedWord := by
  rw [←Fintype.card_sigma]
  let entries : {a //Occupied (tags r slot) a} ≃ Names r :=
    { toFun := Subtype.val
      invFun := fun a=>⟨a,every_label r slot a⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
  exact Fintype.card_congr entries

open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

theorem observed_word {n w K : ℕ} (slot : Slots r↪Fin n) (S : Banks) (m : Memory w)
    (locality : Local (tags r slot) K) :
    S.result (tags r slot) m K (S.starts+n) =
      ((∑v,Fintype.card (r v).UsedWord : ℕ) : Computability.VPVNP.BurstRAM.Word w) :=
  (S.total _ _ locality).trans (congrArg (fun t : ℕ => (t : Computability.VPVNP.BurstRAM.Word w)) (uses_total r slot))

theorem observed {n w K : ℕ} (slot : Slots r↪Fin n) (S : Banks) (m : Memory w)
    (locality : Local (tags r slot) K) (room : n < 2^w) :
    (S.result (tags r slot) m K (S.starts+n)).val = (∑v,Fintype.card (r v).UsedWord:ℕ) := by
  have bounded : (∑v,Fintype.card (r v).UsedWord) ≤ n := by
    rw [← uses_total r slot,← DescentDistinctWindow.count _ locality]
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℕ) := Finset.sum_le_sum fun i _ => by split <;> decide
      _ = n := by simp
  rw [observed_word r slot S m locality]
  exact Fin.val_cast_of_lt (bounded.trans_lt room)

end
end Hierarchy.DescentTerminalPrivateCount

end OAI
