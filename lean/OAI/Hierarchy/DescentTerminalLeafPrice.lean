import OAI.Hierarchy.DescentTerminalLeafDigits

namespace OAI
/-! # Priced physical traversals of the real owners, hidden rows and operand rows -/
namespace Hierarchy.DescentTerminalLeafDigits
open DescentTerminalPrintedFields DescentTerminalRowBooks DescentTerminalScalarHeader
open scoped Classical BigOperators
noncomputable section
variable {q t H N A w V : ℕ}
local notation "C" => Control q t H N A w V
local notation "B" => Book q t H N A w

def refs (b : B) (k : Fin b.2.1.val) : ℕ :=
  ((b.2.2.rows k).map (fun u=>u.2.1.val)).getD 0

def Tidy (c : C) : Prop :=
  ∀v k a n f,(c.2 v).2.2.rows k=some (a,n,f) → ∀j,n.val ≤ j.val → f j=none

/-- Positions are those actually held by the unpadded graph archive. Each
local name is charged at most once per operand occurrence. -/
abbrev SiteField (b : B) :=
  Fin 2 ⊕ (Fin b.1.val ⊕ ((k : Fin b.2.1.val)×(Fin 2 ⊕ Fin (refs b k))))
abbrev Physical (c : C) := Unit ⊕ ((v : Fin c.1.val)×SiteField (c.2 v))

def address (c : C) : Physical c → Coord V H N A
  | .inl _=>.inl ()
  | .inr ⟨v,z⟩=>
    let vv:=v.castLE (Nat.le_of_lt_succ c.1.isLt)
    let b:=c.2 v
    match z with
    | .inl p=>if p=0 then .inr (.inl vv) else .inr (.inr (.inl vv))
    | .inr (.inl h)=>.inr (.inr (.inr (.inl (vv,h.castLE (Nat.le_of_lt_succ b.1.isLt)))))
    | .inr (.inr ⟨k,pos⟩)=>
      let kk:=k.castLE (Nat.le_of_lt_succ b.2.1.isLt)
      match pos with
      | .inl j=>if j=0 then .inr (.inr (.inr (.inr (.inl (vv,kk))))) else
          .inr (.inr (.inr (.inr (.inr (.inl (vv,kk))))))
      | .inr j=>
        have bound : refs b k ≤ A := by
          cases eqn:b.2.2.rows k with
          | none=>simp [refs,eqn]
          | some a=>simpa [refs,eqn] using Nat.le_of_lt_succ a.2.1.isLt
        .inr (.inr (.inr (.inr (.inr (.inr (vv,kk,j.castLE bound))))))

def expense (c : C) := 1+∑v, (2+(c.2 v).1.val+∑k, (2+refs (c.2 v) k))

theorem physical_count (c : C) : Fintype.card (Physical c)=expense c := by
  simp [Physical,SiteField,expense,Fintype.card_sigma,Fintype.card_sum,add_assoc]

theorem coverage (c : C) (clean : Tidy c) (j : Coord V H N A) (live : (digit (emit c) j).val≠0) :
    ∃z : Physical c,address c z=j := by
  let widthRead (b : B) (h : Fin H) : ℕ := (extend b.2.2.width 0 h).val
  let Entry (b : B) := Fin t × Fin (A+1) × (Fin A → Option (Fin q ⊕ Fin b.1.val))
  let roleRead (b : B) (k : Fin N) : ℕ := (((atom b k).map fun z : Entry b =>z.1.succ).getD 0).val
  let arityRead (b : B) (k : Fin N) : ℕ := (((atom b k).map fun z : Entry b =>z.2.1).getD 0).val
  let operandRead (b : B) (k : Fin N) (j : Fin A) : ℕ :=
    (((atom b k).map fun z : Entry b =>ref (Nat.le_of_lt_succ b.1.isLt) (z.2.2 j)).getD 0).val
  rcases j with u| (v| (v| (⟨v,h⟩| (⟨v,k⟩| (⟨v,k⟩|⟨v,k,j⟩)))))
  · exact ⟨.inl (),by cases u;rfl⟩
  all_goals
    have hv : v.val<c.1.val := by
      by_contra outside
      apply live
      have vacant : fill c v=emptyBook q t H N A w := by simp [fill,extend,outside]
      first | change (fill c v).1.val=0 | change (fill c v).2.1.val=0
            | change widthRead (fill c v) h=0 | change roleRead (fill c v) k=0
            | change arityRead (fill c v) k=0 | change operandRead (fill c v) k j=0
      rw [vacant];
        simp [widthRead,roleRead,arityRead,operandRead,emptyBook,atom,extend] <;> rfl
  all_goals let i : Fin c.1.val:=⟨v.val,hv⟩
  all_goals have book : fill c v=c.2 i := by simp [fill,extend,hv,i]
  · exact ⟨.inr ⟨i,.inl 0⟩,rfl⟩
  · exact ⟨.inr ⟨i,.inl 1⟩,rfl⟩
  · by_cases hh : h.val<(c.2 i).1.val
    · exact ⟨.inr ⟨i,.inr (.inl ⟨h.val,hh⟩)⟩,rfl⟩
    · exact False.elim (live (by simp [digit,emit,book,extend,hh]))
  all_goals
    have hk : k.val<(c.2 i).2.1.val := by
      by_contra outside
      apply live
      first | change roleRead (fill c v) k=0 | change arityRead (fill c v) k=0
            | change operandRead (fill c v) k j=0
      rw [book]
      have missing : atom (c.2 i) k=none := by simp [atom,extend,outside]
      simp only [roleRead,arityRead,operandRead,missing,Option.map_none,Option.getD_none,Fin.val_zero]
  all_goals let a : Fin (c.2 i).2.1.val:=⟨k.val,hk⟩
  · exact ⟨.inr ⟨i,.inr (.inr ⟨a,.inl 0⟩)⟩,rfl⟩
  · exact ⟨.inr ⟨i,.inr (.inr ⟨a,.inl 1⟩)⟩,rfl⟩
  · by_cases hj:j.val<refs (c.2 i) a
    · exact ⟨.inr ⟨i,.inr (.inr ⟨a,.inr ⟨j.val,hj⟩⟩)⟩,rfl⟩
    · exfalso
      apply live
      change operandRead (fill c v) k j=0
      rw [book]
      have read : atom (c.2 i) k=(c.2 i).2.2.rows a:=by simp [atom,extend,hk,a]
      simp only [operandRead,read]
      cases cut:(c.2 i).2.2.rows a with
      | none=>rfl
      | some z=>
        have late : z.2.1.val ≤ j.val := by simpa [refs,cut] using Nat.le_of_not_gt hj
        simp [clean i a _ _ _ cut j late,ref]

theorem sparse_count (c : C) (clean : Tidy c) :
    Fintype.card {j : Coord V H N A // (digit (emit c) j).val≠0} ≤ expense c := by
  rw [←physical_count]
  let embed : {j : Coord V H N A // (digit (emit c) j).val≠0} ↪ Physical c :=
    ⟨fun j=>(coverage c clean j.val j.property).choose,fun a b e=>Subtype.ext
      ((coverage c clean a.val a.property).choose_spec.symm.trans
        ((congrArg (address c) e).trans (coverage c clean b.val b.property).choose_spec))⟩
  exact Fintype.card_le_of_injective _ embed.injective

end
end Hierarchy.DescentTerminalLeafDigits

end OAI
