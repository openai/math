import OAI.Optimization.LinearProgramming.PrimalDual.Gather

/-! A fixed sequence of strided gathers reads below a boundary and writes disjoint
dense windows above it. This is used to unpack both oracle returns. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open RAM RAM.Block RAM.Tape

structure Move where
  stride : Nat
  src : Nat
  dst : Nat
  count : Nat
  deriving DecidableEq, Repr

namespace Move

def ticks (a : Nat → Nat) (v : Move) := a v.count*(v.stride+6)+5

def room (a : Nat → Nat) (edge : Nat) (v : Move) : Prop :=
  6 ≤ v.src ∧ 6 ≤ v.dst ∧ 6 ≤ v.count ∧ 0 < v.stride ∧
  a v.src+v.stride*a v.count ≤ edge ∧ edge ≤ a v.dst ∧
  ∀ j < a v.count, a v.src+v.stride*j ≠ 1

def apart (a : Nat → Nat) (v w : Move) : Prop :=
  a v.dst+a v.count ≤ a w.dst ∨ a w.dst+a w.count ≤ a v.dst

def pack : List Move → Block
  | [] => .skip
  | v::vs => .seq (gather v.stride v.src v.dst v.count) (pack vs)

/-- Execute each sealed move on its real cursors. Every output word is compared
with the original source, even when a later move reuses a source channel. -/
theorem pack_correct {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {P : K → Prop} (vs : List Move) (a : Nat → Nat) (edge : Nat) (s : Memory K)
    (hs : Good P s) (hindex : ∀ r, 6 ≤ r → s.index r = a r) (he : 2 ≤ edge)
    (hroom : ∀ v ∈ vs, room a edge v) (hsep : vs.Pairwise (apart a)) :
    ∃ t, Eval (Good P) (pack vs) s ((vs.map (ticks a)).sum) t ∧
      (∀ v ∈ vs, ∀ j < a v.count, t.data (a v.dst+j) = s.data (a v.src+v.stride*j)) ∧
      (∀ z, z ≠ 1 → (∀ v ∈ vs, z < a v.dst ∨ a v.dst+a v.count ≤ z) → t.data z = s.data z) ∧
      ∀ r, 6 ≤ r → t.index r = s.index r := by
  induction vs generalizing s with
  | nil => exact ⟨s,.skip hs,by simp,fun _ _ _ => rfl,fun _ _ => rfl⟩
  | cons v vs ih =>
    obtain ⟨ha,hd,hn,hst,low,high,ns⟩ := hroom v (by simp)
    obtain ⟨u,first,get,frame,idx⟩ := gather_correct v.stride v.src v.dst v.count
      (a v.src) (a v.dst) (a v.count) s hs ha hd hn (hindex _ ha) (hindex _ hd) (hindex _ hn)
      hst ns (he.trans high) (low.trans high)
    have tailRoom : ∀ w ∈ vs, room a edge w := fun w hw => hroom w (.tail _ hw)
    obtain ⟨t,rest,more,untouched,tailIndex⟩ := ih u first.safe_end
      (fun r hr => (idx r hr).trans (hindex r hr)) tailRoom (List.pairwise_cons.mp hsep).2
    refine ⟨t,by simpa [pack,ticks] using first.seq rest,?_,?_,
      fun r hr => (tailIndex r hr).trans (idx r hr)⟩
    · intro w hw j hj
      rcases List.mem_cons.mp hw with rfl | hw
      · exact (untouched _ (by omega) (fun y hy => by
          rcases (List.pairwise_cons.mp hsep).1 y hy with left|right
          · exact .inl (by omega)
          · exact .inr (by omega))).trans (get j hj)
      · obtain ⟨_,_,_,st,endSrc,_,avoid⟩ := tailRoom w hw
        have hlt : a w.src + w.stride*j < edge := by
          have := Nat.mul_lt_mul_of_pos_left hj st
          omega
        exact (more w hw j hj).trans (frame _ (avoid j hj) (.inl (by omega)))
    · intro z hz outside
      exact (untouched z hz (fun w hw => outside w (.tail _ hw))).trans
        (frame z hz (outside v (by simp)))

end Move
end PrimalDual
end LinearProgramming
end Optimization
end OAI
