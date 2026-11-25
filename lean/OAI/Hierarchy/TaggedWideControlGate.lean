import OAI.Hierarchy.TaggedShorterControlHistory
import OAI.ThreeFlat.BitNetwork.UsedHidden

namespace OAI
/-! # Binary pins and physical price of one native control verifier -/

noncomputable section
namespace Hierarchy.Tagged.WideControlJoin
open ThreeFlat Routing Diagonal TraceRows TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory TaggedShorterControlHistory
open scoped Classical BigOperators

/-- All parameters of an actual machine, its finite array and the 28 tagged sort slices. -/
structure Gate where
  W : ℕ
  p : ℕ
  r : ℕ
  k : ℕ
  S : ℕ
  f : ℕ
  u : ℕ
  m : ℕ
  machine : Machine W p r k
  word : 3≤W+1
  labels : p≤2^(W+1)
  start : Word W
  addr : Fin u→Word W
  headerBound : S≤2^W
  clock : f+u≤2^(W+1)

namespace Gate
variable {F : Type*} [Field F] (G : Gate)

abbrev Head := Fin G.S × Fin (G.W+1)
abbrev Seen := Fin G.u × Fin (G.W+1)
abbrev Hidden := TaggedShorterClock.Pin G.W G.r G.f ⊕ G.Seen ⊕ Hole G.m 28
abbrev Pin := TaggedShorterControlHistory.Pin G.S G.f G.u G.W G.r G.m 28

theorem high : G.S≤2^(G.W+1) := G.headerBound.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))

def hardware := (TaggedShorterControlHistory.network (F:=F) (m:=G.m) (a:=28)
  G.machine G.word G.labels G.start G.high G.clock (wide ∘ G.addr)).compactHidden

def seenPin (j : G.Seen) : G.Hidden := .inr (.inl j)
def sortPin (i : Fin 28) (j : Fin (pins G.m G.m)) : G.Hidden := .inr (.inr (i,j))

def input (head : G.Head→Bool) (y : G.Hidden→Bool) : G.Pin→Bool :=
  Sum.elim (Sum.elim head (Sum.elim (y ∘ Sum.inl) (y ∘ G.seenPin))) (y ∘ Sum.inr ∘ Sum.inr)

def value (head : G.Head→Bool) (y : G.Hidden→Bool) : F :=
  TypedWiring.value (G.hardware (F:=F)) (G.input head y)

def sorts (y : G.Hidden→Bool) : F := ∏ j,coeff F G.m G.m (y ∘ G.sortPin j)

def headBits (header : ℕ→Word G.W) (i : G.Head) := TraceWords.bits (wide (header i.1.val)) i.2

def zeroFlag (flag : Fin G.u) (y : G.Seen→Bool) : F :=
  if ∀ j : Fin (G.W+1), y (flag,j)=false then 1 else 0

theorem hidden_card : Fintype.card G.Hidden =
    G.f*((5+G.r)*(G.W+1)) + G.u*(G.W+1) + 28*pins G.m G.m := by
  simp [Hidden,TaggedShorterClock.Pin,Hole,Tagged.ControlSort.Hole,Nat.add_assoc]

end Gate
end Hierarchy.Tagged.WideControlJoin

end
end OAI
