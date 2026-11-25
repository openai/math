import OAI.Computability.IntegerMultiplication.Olive.Roses
import OAI.Computability.IntegerMultiplication.Olive.Grove

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Olive
open Well Larch Bureau Halo Moira Param Scale Strip Code Rivulet Dusk Grid
open Echo Cone Cap Brief Staff IntegerMultiplication.Fourier Dial
open Finset
variable {I:Type}(n:I→ℕ){r:Regime I}(T:Origin n r)
variable (h:∀i,Season (n i))
variable (N:I→ℕ)(a:Realizes r N) (f:I→ℝ)(hf:∀ i,1≤f i)
-- orbit over histories, preserve x as separate. generic term
abbrev Fx i:= Farm (n i)
abbrev Tr i:= Fx n i × Fx n i
noncomputable section
variable (o:(i:I)→Fin (N i)→Fx n i→Fx n i)
abbrev Rz i (v:Tr n i):Tree := Tree.fork (flat (h i) v.1) (flat (h i) v.2)
abbrev Score (i:I)(j:Fin (N i))(x:Tr n i):Tr n i:= (x.1,o i j x.1+x.2)
abbrev Ctx:= Well.PxB N (Tr n)
abbrev rctx:= Well.S0 N a (Tr n)
abbrev pivot:=Well.center N (Tr n)
abbrev formula (v:Ctx n N) : Fx n (pivot n N v) :=
  o (pivot n N v) (Dial.focus N v) v.1.value.1
abbrev tokenx (v:Ctx n N)(x: Fx n (pivot n N v)):= flat (h (pivot n N v)) x
-- Kit
abbrev Ticket :=
  Mid (n ∘ pivot n N) (rctx n N a) (f ∘ pivot n N)
    (fun v=> tokenx n h N v (v.1.value.1))
    (fun v=> tokenx n h N v (formula n N o v))

theorem value0 (x:(i:I)→Tr n i) : close n (fun i=>Rz n h i (x i)) :=
  (sedan n h (fun i=>(x i).1)).fork (sedan n h (fun i=>(x i).2)) (chargep n)
include a T hf
set_option maxHeartbeats 500000 in
theorem circulate (k:Ticket n h N a f o) (x:(i:I)→Tr n i):
    Mid n r (fun i=> f i*(N i+1)) (fun i=>Rz n h i (x i)) (fun i=>Rz n h i
      (Dial.iter N (Score n N o) (Dial.start N ⟨i,x i⟩))) := by
  let V:=Ctx n N
  let y:=pivot n N
  let m:=n ∘ y
  let g:=f ∘ y
  let t : (i:V)→Season (m i):= fun i=>h (y i)
  let R := rctx n N a
  have T0:= slid T N a (Tr n) -- omit f arg?
  have e(i:V):= hf (y i)
  change ∀i:V,1≤g i at e
  let X (i:V):=i.1.value.1; let Y(i:V):=i.1.value.2
  let X':=formula n N o
  let w(i:V):Tr m i:= (X i,Y i)
  let b(i:V):=Rz m t i (w i)
  have s:=Well.launch e (IntegerMultiplication.Well.self T0 (value0 m t w))
  change Mid m R g b (together (LandN m t X) (LandN m t Y)) at s
  have p:=s.out
  let d:=Carries.dropRight s.budget (Volume.left p) (Volume.right p)
  let u:=Carries.dropLeft s.budget (Volume.left p) (Volume.right p)
  refine IntegerMultiplication.Well.sweep T hf N a (Tr n) (Rz n h) (Score n N o) x
    (value0 (n∘(Sigma.fst:Sigma (Tr n)→I)) (fun i=>h i.1) (fun i=>i.2)) ?_
  have E:=Well.pipe (s.chain d) k
  have M:= E.twice (s.chain u)
  have U := (flower m t X' Y).larger (allow_ m e)
  exact (s.chain d).twice (M.chain U)

-- sums value
omit T hf a
set_option maxHeartbeats 1000000 in
theorem comb (i:I)(v:Fx n i)(z:Fx n i):
    Dial.iter N (Score n N o) (Dial.start N ⟨i,(v,z)⟩)=
      (v, (∑ j:Fin (N i),o i j v)+z) := by
  apply Eq.trans (Well.result N (Tr n) (Score n N o) i (v,z))
  suffices p: ∀ k (u:Fin k→ Fin (N i)), (List.ofFn u).foldr (Score n N o i) (v,z)= (v, (∑ j:Fin k,o i (u j) v)+z) from p (N i) id
  intro k u
  induction k with
  | zero=>simp only [List.ofFn_zero,List.foldr_nil, Finset.univ_eq_empty,sum_empty,zero_add]
  | succ k ih=>
    rw [List.ofFn_succ,List.foldr_cons,ih,Fin.sum_univ_succ]
    unfold Score; dsimp only; rw [add_assoc]

include T hf a
set_option maxHeartbeats 450000 in
theorem reserve (k:Ticket n h N a f o) (x:(i:I)→Fx n i) :
    Mid n r (fun i=>f i*(N i+1)) (LandN n h x)
      (LandN n h (fun i=> ∑ j:Fin (N i),o i j (x i))) := by
  let t(i:I): Tr n i := (x i,0)
  let y(i:I):= ∑ j:Fin (N i),o i j (x i)
  have e (i):
      Rz n h i (Dial.iter N (Score n N o) (Dial.start N ⟨i,t i⟩)) =
        Tree.fork (LandN n h x i) (LandN n h y i):= by
    unfold t; rw [comb n N o i (x i) 0,add_zero]
  have P:= circulate n T h N a f hf o k t
  have A(i:I):= one_le_mul_of_one_le_of_one_le (hf i) (by simp : (1:ℝ)≤ (N i)+1)
  have Z:= IntegerMultiplication.Well.self T (sedan n h x)
  have D:= Well.launch A (Z.twice (Z.chain (erase n h x)))
  change Mid _ _ _ (LandN n h x) (fun i=> Rz n h i (t i)) at D
  have L:= Well.pipe D P
  simp_rw [e] at L
  exact L.chain (Carries.dropLeft L.budget (Volume.left L.out) (Volume.right L.out))
end
end Olive

end IntegerMultiplication
end Computability
end OAI
