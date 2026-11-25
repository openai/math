import OAI.Hierarchy.DescentKernelHistory

namespace OAI
/-! # One shared bounded key for the scalar of any retained local history -/

namespace Hierarchy.DescentKernelHistory
open scoped BigOperators Classical
noncomputable section

variable {F : Type*} [CommSemiring F]
variable {b t h n a w : ℕ}

/-- Fixed tables of short local ordinals. The sentinel width zero has a
unique possible word, and an unused row has no scalar factor. -/
@[ext] structure AddressBook (b t h n a w : ℕ) where
  width : Fin h→Fin (w+1)
  rows : Fin n→Option (Fin t × Fin (a+1) × (Fin a→Option (Fin b ⊕ Fin h)))
  deriving Fintype

def AddressBook.read (s : AddressBook b t h n a w) (scalar : Fin t→List (List Bool)→F)
    (x : Fin b→List Bool) : F :=
  ∑ y : (j : Fin h)→Word (s.width j).val, ∏i : Fin n,match s.rows i with
    | none=>1
    | some (tag,count,ref)=>scalar tag (List.ofFn fun j : Fin count.val=>
      (ref ⟨j.val,j.isLt.trans_le (Nat.le_of_lt_succ count.isLt)⟩).elim []
        (fun q=>q.elim x (fun k=>wordList (y k))))

theorem AddressBook.size :
    Fintype.card (AddressBook b t h n a w)=(w+1)^h*(1+t*(a+1)*(b+h+1)^a)^n := by
  let e : AddressBook b t h n a w ≃ (Fin h→Fin (w+1)) ×
      (Fin n→Option (Fin t × Fin (a+1) × (Fin a→Option (Fin b ⊕ Fin h)))) :=
    ⟨fun s=>(s.width,s.rows),fun p=>⟨p.1,p.2⟩,fun _=>rfl,fun _=>rfl⟩
  rw [Fintype.card_congr e]
  simp [Nat.add_comm,Nat.mul_assoc]

variable {Tag B : Type} (r : Recipe Tag B) (tags : Tag→Fin t) (boundary : B→Fin b)
variable (hidden : r.Hidden ≃ Fin h) (node : r.Node ≃ Fin n)
variable (large : ∀j,r.width j≤w) (slots : ∀i,r.arity i≤a)

/-- Actual numbered operand references of the old recipe. Outside the arity
only, the cursor is padded by a distinguished empty slot. -/
def encode : AddressBook b t h n a w where
  width j := ⟨r.width (hidden.symm j),Nat.lt_succ_of_le (large _)⟩
  rows i :=
    let v := node.symm i
    some (tags (r.tag v),⟨r.arity v,Nat.lt_succ_of_le (slots v)⟩, fun j=>
      if bounded : j.val<r.arity v then some ((r.operand v ⟨j.val,bounded⟩).map boundary hidden) else none)

private def relabel (f : r.Hidden≃Fin h) :
    ((i : r.Hidden)→Word (r.width i)) ≃ ((j : Fin h)→Word (r.width (f.symm j))) :=
  (Equiv.piCongrLeft' (fun i=>Word (r.width i)) f)

/-- The key determines the exact contraction value for all exterior words.
Private numbering and node order only permute the finite sum and product. -/
theorem encode_read (scalar : Fin t→List (List Bool)→F)
    (x : Fin b→List Bool) :
    (encode r tags boundary hidden node large slots).read scalar x=
      r.value (fun v=>scalar (tags v)) (x∘boundary) := by
  let e:=relabel r hidden
  let val (y : (j : Fin h)→Word (r.width (hidden.symm j))) (i : Fin n) : F :=
    match (encode r tags boundary hidden node large slots).rows i with
    | none=>1
    | some (tag,count,ref)=>scalar tag (List.ofFn fun j : Fin count.val=>
        (ref ⟨j.val,j.isLt.trans_le (Nat.le_of_lt_succ count.isLt)⟩).elim []
          (fun q=>q.elim x (fun k=>wordList (y k))))
  change (∑ y,∏ i,val y i)=_
  rw [←e.sum_comp (fun y=>∏i,val y i)]
  unfold Recipe.value
  apply Finset.sum_congr rfl
  intro y _
  let value (v : r.Node) := scalar (tags (r.tag v)) (List.ofFn fun j=>
    (r.operand v j).elim (x∘boundary) (fun i=>wordList (y i)))
  change (∏i,val (e y) i)=∏v,value v
  rw [←node.symm.prod_comp value]
  apply Finset.prod_congr rfl
  intro i _
  dsimp only [value]
  simp only [val,encode,dite_eq_left,Fin.is_lt]
  congr 2
  funext j
  cases eq : r.operand (node.symm i) j with
  | inl q => simp []
  | inr q =>
    change wordList (y (hidden.symm (hidden q)))=wordList (y q)
    exact congrArg (fun z : r.Hidden=>wordList (y z)) (hidden.symm_apply_apply q)

end
end Hierarchy.DescentKernelHistory

end OAI
