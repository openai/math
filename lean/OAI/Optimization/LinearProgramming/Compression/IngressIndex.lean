import OAI.Optimization.LinearProgramming.Compression.IngressCore

/-! Short address-only subroutines for bootstrapping the online request tape. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Ingress
open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Store the word in `src` at the current pointer, then advance the pointer. -/
def writeWord (ptr src : ℕ) : Block := .seq (.op (.addrStore ptr src)) (.op (.incr ptr ptr))

theorem writeWord_spec (P : K → Prop) (s : Memory K) (ptr src : ℕ)
    (h : s.index ptr ≠ ptr) (hs : Good P s) :
    ∃ t, Block.Eval (Good P) (writeWord ptr src) s 2 t ∧ t.data=s.data ∧
      t.index ptr=s.index ptr+1 ∧ t.index (s.index ptr)=s.index src ∧
      ∀ i, i≠ptr → i≠s.index ptr → t.index i=s.index i := by
  let a := s.putIndex (s.index ptr) (s.index src)
  let t := a.putIndex ptr (a.index ptr+1)
  have e : Block.Eval (Good P) (.op (.addrStore ptr src)) s 1 a := Block.Eval.op_addrStore _ _ _ hs hs
  have e' : Block.Eval (Good P) (.op (.incr ptr ptr)) a 1 t := Block.Eval.op_incr _ _ _ hs hs
  refine ⟨t,e.seq e',rfl,by simp [t,a,Ne.symm h],by simp [t,a,h],?_⟩
  intro i hi hi'; simp [t,a,hi,hi']

/-- Increase or decrease an address by a fixed compile-time number of unit instructions. -/
def walk (back : Bool) (ptr amount : ℕ) : Block :=
  .straight (List.replicate amount (if back then .decr ptr ptr else .incr ptr ptr))

theorem walk_spec (P : K → Prop) (s : Memory K) (back : Bool) (ptr amount : ℕ) (hs : Good P s) :
    ∃ t, Block.Eval (Good P) (walk back ptr amount) s amount t ∧ t.data=s.data ∧
      t.index ptr=(if back then s.index ptr-amount else s.index ptr+amount) ∧
      ∀ i, i≠ptr → t.index i=s.index i := by
  induction amount generalizing s with
  | zero => exact ⟨s,.skip hs,rfl,by split <;> simp,fun _ _ => rfl⟩
  | succ j ih =>
    let a := s.putIndex ptr (if back then s.index ptr-1 else s.index ptr+1)
    have ea : Block.Eval (Good P) (.op (if back then .decr ptr ptr else .incr ptr ptr)) s 1 a := by
      cases back with
      | false => exact Block.Eval.op_incr _ _ _ hs hs
      | true => exact Block.Eval.op_decr _ _ _ hs hs
    obtain ⟨t,et,hd,hp,hf⟩ := ih a ea.safe_end
    refine ⟨t,?_,hd,?_,?_⟩
    · simpa [walk, List.replicate_succ, Block.straight, Nat.one_add] using ea.seq et
    · cases back <;> simp [a,Nat.sub_sub] at hp ⊢ <;> omega
    · intro i hi; simpa [a,hi] using hf i hi

/-- Encode the saved scalar tag in address register one. Both branch paths take three
instructions. Only the address register that formerly held the order is overwritten. -/
def selectTag : Block :=
  .seq (.op (.addrConst 1 0)) (.branch (.scalarLT 6 3) .skip (.op (.addrConst 1 1)))

theorem selectTag_spec (P : K → Prop) (s : Memory K) (tag : ℕ) (hbit : tag≤1)
    (h6 : s.data 6=(tag:K)) (h3 : s.data 3=1) (hs : Good P s) :
    ∃ t, Block.Eval (Good P) selectTag s 3 t ∧ t.data=s.data ∧ t.index 1=tag ∧
      ∀ i, i≠1 → t.index i=s.index i := by
  let a := s.putIndex 1 0
  have ea : Block.Eval (Good P) (.op (.addrConst 1 0)) s 1 a := Block.Eval.op_addrConst _ _ _ hs hs
  have cases' : tag=0 ∨ tag=1 := by omega
  rcases cases' with rfl | rfl
  · have test : (Cond.scalarLT 6 3).test a = true := by simp [Cond.test,a,h6,h3]
    exact ⟨a,ea.seq (.branchTrue test (.skip hs)),rfl,by simp [a],fun i hi => by simp [a,hi]⟩
  · let t := a.putIndex 1 1
    have et : Block.Eval (Good P) (.op (.addrConst 1 1)) a 1 t := Block.Eval.op_addrConst _ _ _ hs hs
    have test : (Cond.scalarLT 6 3).test a = false := by simp [Cond.test,a,h6,h3]
    exact ⟨t,ea.seq (.branchFalse test et),rfl,by simp [t],fun i hi => by simp [t,a,hi]⟩

end Ingress
end Compression
end LinearProgramming
end Optimization
end OAI
