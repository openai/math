import OAI.Computability.IntegerMultiplication.Ask.Search
import OAI.Computability.IntegerMultiplication.Strip.Index

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Ask
open Strip Code Iter Bits
variable {I X:Type} [Codec X] {p:I→Tree} {r:Regime I} {L:I→ℕ}
variable {A:I→Type} (s:(i:I)→Series (A i))
variable (t:I→Tab (X:=X)) (u:(i:I)→ A i→Word)
variable (σ : Rip r (fun i=>(s i).count) L p (fun i=>send (t i)))
    (ρ : Rip r (fun i=>(s i).count) L p r.header)
    (h : Strip.Trace r s (fun i a=>send (u i a)))
variable (A₀ : ∃ C:ℕ,∀i,size (t i)≤ C*(L i+1))
    (A₁ : ∃ C:ℕ,∀ i a,((t i).length+1)*Code.size (u i a) ≤ C*(L i+1))
include σ ρ h A₀ A₁
theorem deal (x₀ : X) :
    Rip r (fun i=>(s i).count) L p (stackRun s (fun i a=>send (label x₀ (u i a) (t i)))) := by
  let N i := (s i).count; let K := mass r N L
  obtain ⟨c,v⟩ := (Strip.Station.supply (n:=N) (l:=L) h.valid (fun _=>le_rfl))
  have l := ρ.chain (Rip.monoSize h.offer (fun _=> le_refl _) (fun i=> Nat.zero_le (L i)))
  obtain ⟨k,d⟩ := ρ.chain (show Rip r N L r.header _ from ⟨_,v⟩) |>.twice σ
  obtain ⟨C,A₀⟩ := A₀; obtain ⟨D,A₁⟩ := A₁
  have E i : (N i:ℝ)*((L i:ℝ)+1)≤K k i := by
    unfold K mass; gcongr
    exact one_le_pow₀ (by simp)
  have τ : Carries (K k) p (stackRun s (fun i _=>Code.send (t i))) := by
    apply Strip.spread s _ d
    refine ⟨2*C,fun i=>?_⟩
    change ((N i:ℝ)+1)*(Code.size (t i):ℝ) ≤ _
    have a : (1:ℝ) ≤ N i := by exact_mod_cast h.valid.1 i
    apply le_trans _ (mul_le_mul_of_nonneg_left (E i) (by positivity : (0:ℝ)≤↑(2*C:ℕ)))
    push_cast
    have e : (Code.size (t i):ℝ) ≤ (C:ℝ)*((L i:ℝ)+1) := by exact_mod_cast A₀ i
    calc
     _ ≤ (2*(N i:ℝ))*((C:ℝ)*((L i:ℝ)+1)) := by gcongr; linarith
     _ = _ := by ring
  have h₁ := Rip.coalesce (n:=N) (l:=L) (fun i a=> send (u i a)) (fun i _=> send (t i)) l ⟨k,τ⟩
  let q0 (i : Sigma A) := t i.fst
  let u0 (i: Sigma A) := u i.1 i.2
  let W (i : I) : ℝ := L i+1
  let Z := Sigma A
  let Q := W ∘ (Sigma.fst (β:=A))
  let V i a := Tree.fork (send (u i a)) (send (t i))
  have Small : Volume Q (fun i:Z=> V i.1 i.2) := by
    refine ⟨D+C+1,fun i=>?_⟩
    have E1 : size (u i.1 i.2) ≤ D*(L i.1+1) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos ((t i.1).length)) |>.trans (A₁ _ _)
    have e:= A₀ i.1
    unfold V Q W; dsimp only [Function.comp_apply,Tree.count]
    change ((size (u i.1 i.2)+size (t i.1)+1:ℕ):ℝ) ≤ _
    exact_mod_cast (show size (u0 i)+size (q0 i)+1 ≤ (D+C+1)*(L i.1+1) from by unfold u0 q0; nlinarith)
  have T := Carries.idles (show ∀ i, 1 ≤ Q i from fun i=>by dsimp only [Q,W,Function.comp_apply]; simp) Small
  have U : Carries Q (fun i:Z=> V i.1 i.2) _ := Ask.find x₀ q0 u0
    (T.chain (Carries.dropRight T.budget (Volume.left Small) (Volume.right Small)))
    (T.chain (Carries.dropLeft T.budget (Volume.left Small) (Volume.right Small)))
    ⟨D,fun i=> by change (_+1:ℝ)*_ ≤ (D:ℝ)*((L i.1:ℝ)+1); exact_mod_cast A₁ i.1 i.2⟩
  have Y := liftoff s V (fun i a=> send (label x₀ (u i a) (t i))) W U
  refine h₁.chain ⟨k,Y.times (d.budget) 2 ?_⟩
  intro i
  change _ ≤ (2:ℕ)*K k i
  have a := d.budget i
  dsimp only [W]
  norm_num
  change (N i:ℝ)*((L i:ℝ)+1)+1 ≤ _
  linarith [E i]
end Ask

end IntegerMultiplication
end Computability
end OAI
