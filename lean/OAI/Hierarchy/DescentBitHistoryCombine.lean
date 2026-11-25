import OAI.Hierarchy.DescentBoundedBitHistory

namespace OAI
/-! # Product and private-label contraction for normalized bit recipes -/

namespace Hierarchy.DescentKernelHistory.BitRecipe
open scoped Classical BigOperators
noncomputable section
variable {Tag F J A H : Type} [CommSemiring F] [Fintype J] [Fintype H] {B : J→Type}
variable {bw : (i:J)→B i→ℕ} (old : ∀i,BitRecipe Tag (B i) (bw i))
variable {w : A→ℕ} (hw : H→ℕ) (route : ∀i,BitRef (bw i)→BitRef w ⊕ BitRef hw)
abbrev Private := H ⊕ (Σi,(old i).Hidden)
def privateWidth : Private (H:=H) old→ℕ := Sum.elim hw (fun p=>(old p.1).hiddenWidth p.2)

def combineBits : BitRecipe Tag A w where
  Hidden := Private (H:=H) old
  hiddenWidth := privateWidth old hw
  Node := Σi,(old i).Node
  tag u := (old u.1).tag u.2
  arity u := (old u.1).arity u.2
  size u := (old u.1).size u.2
  arg u j t := match (old u.1).arg u.2 j t with
    | .inr ⟨e,s⟩=>.inr ⟨.inr ⟨u.1,e⟩,s⟩
    | .inl e=>match route u.1 e with
      | .inl q=>.inl q
      | .inr ⟨q,s⟩=>.inr ⟨.inl q,s⟩

def hiddenAssignments : ((i : Private (H:=H) old)→Word (privateWidth old hw i)) ≃
    ((i:H)→Word (hw i))×((i:J)→(e:(old i).Hidden)→Word ((old i).hiddenWidth e)) where
  toFun f := (fun i=>f (.inl i),fun i e=>f (.inr ⟨i,e⟩))
  invFun f
    | .inl i=>f.1 i
    | .inr ⟨i,e⟩=>f.2 i e
  left_inv f := by funext i;rcases i with _|⟨_,_⟩ <;> rfl
  right_inv _ := rfl

theorem combine_bits_value (scalar : Tag→List (List Bool)→F) (x : BitRef w→Bool) :
    (combineBits old hw route).value scalar x=∑hidden : (i:H)→Word (hw i),
      ∏i,(old i).value scalar (fun z=>(route i z).elim x (fun b=>hidden b.1 b.2)) := by
  unfold value
  let r := combineBits old hw route
  let f := fun h : (e : Private (H:=H) old)→Word (privateWidth old hw e)=>
    ∏u : r.Node,scalar (r.tag u) (List.ofFn fun j=>wordList fun t=>(r.arg u j t).elim x (fun e=>h e.1 e.2))
  let eqv := hiddenAssignments old hw
  trans ∑a,f a
  · apply Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
    intro a _
    rfl
  calc
    ∑a,f a=∑v,f (eqv.symm v) := (eqv.symm.sum_comp f).symm
    _=_ := ?_
  rw [Fintype.sum_prod_type]
  dsimp only [f,eqv,r]
  apply Finset.sum_congr rfl
  intro h _
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [←Fintype.prod_sigma']
  apply Finset.prod_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
  rintro ⟨i,u⟩ _
  apply congrArg (scalar ((old i).tag u))
  apply congrArg List.ofFn
  funext j
  apply congrArg wordList
  funext t
  cases entry : (old i).arg u j t with
  | inl v=>cases dest : route i v <;> simp [combineBits,entry,dest,hiddenAssignments]
  | inr v=>rcases v with ⟨e,s⟩;simp [combineBits,entry,hiddenAssignments]

theorem combine_bits_refs (i : J) (u : (old i).Node) :
    (combineBits old hw route).nodeBits ⟨i,u⟩=(old i).nodeBits u := rfl

end
end Hierarchy.DescentKernelHistory.BitRecipe

end OAI
