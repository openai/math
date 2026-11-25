import OAI.Computability.IntegerMultiplication.Ask.Deal
import OAI.Computability.IntegerMultiplication.Match
import OAI.Computability.IntegerMultiplication.Strip.Breeze

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Ask
open Code Bits Strip Loom
variable {I X Y Z : Type} {r:Regime I} {N k w : I→ℕ} {f:I→ℝ}
variable [Codec X] [Codec Y] [Codec Z] {A C : I→Type}
section simple
variable (s:(i:I)→Series (C i))
    (x:(i:I)→C i→Y) (a : I→X) (q:I→Y × X→Z)
    (c : ∃ D:ℕ, ∀ i y,size (x i y)≤ D*(w i+1))
    (e : ∃ D:ℕ, ∀ i,size (a i)≤ D*(w i+1))
    (h : Carries (fun i:Sigma C=> (w i.1+1:ℝ)*f i.1)
      (fun i=>send (x i.1 i.2,a i.1)) (fun i=> send (q i.1 (x i.1 i.2,a i.1))))
    (b : ∀ i,1≤f i)
include c e h b
-- broadcast weights over one row. overhead table.length times W.
theorem weight :
    let V := fun i=> (((s i).count+1:ℝ)*((w i:ℝ)+1))*f i
    Carries V (fun i=>Tree.fork (send (a i)) (strip (s i) (x i)))
      (fun i=> strip (s i) (fun y=> q i (x i y,a i))) := by
  obtain ⟨d,c⟩ := c
  obtain ⟨l,e⟩ := e
  let W (i:I) : ℝ := w i+1
  let V i := (((s i).count+1:ℝ)*W i)*f i
  let A (i:I) := send (a i)
  let T i := strip (s i) (x i)
  let K := together A T
  have ss (i:I) : 1 ≤ (s i).count+1 ∧ (1:ℝ)≤(s i).count+1 := by constructor <;> simp
  have s0 (i:I) : 1≤ W i := by simp [W]
  have s₁ (i:I) : (1:ℝ)≤ ((s i).count+1)*W i := one_le_mul_of_one_le_of_one_le (ss i).2 (s0 i)
  have s₂ (i:I) : 1≤V i := one_le_mul_of_one_le_of_one_le (s₁ i) (b i)
  have law (i:I) : ((s i).count+1:ℝ)*W i ≤ V i :=
    le_mul_of_one_le_right (le_trans (by norm_num) (s₁ i)) (b i)
  have law₂ (i:I) : W i≤V i :=
    (le_mul_of_one_le_left (by dsimp only [W]; positivity) (ss i).2).trans (law i)
  have τ : Volume V A :=
    ⟨l,fun i=> (show ((A i).count:ℝ)≤ (l:ℝ)*W i by unfold W; change (size (a i):ℝ) ≤ _; exact_mod_cast e i).trans (by gcongr; exact law₂ i)⟩
  have M : Volume V T := by
    have h : Volume (fun i:Sigma C=> W i.1) (fun i=>send (x i.1 i.2)) :=
      ⟨d,fun i=> by change (size (x i.1 i.2):ℝ)≤↑d*((w i.1:ℝ)+1); exact_mod_cast c i.1 i.2⟩
    obtain ⟨D,f⟩ := stripe_volume s (fun i y=>send (x i y)) W h s0
    refine ⟨D,fun i=> (f i).trans ?_⟩
    gcongr
    calc
     _ ≤ ((s i).count+1)*W i := by have := s0 i; nlinarith
     _ ≤ _ := law i
  have pa := Carries.dropRight (p:=A) s₂ τ M
  have pt := Carries.dropLeft (p:=A) s₂ τ M
  have P := pt
  change Carries _ _ (fun i=>stripe (s i) _) at P
  simp_rw [stripe_eq'] at P
  have U := (P.chain (Carries.func (y:=fun i=>(s i).tab (x i)) s₂ P.out Code.ruler (Easy.ruler Easy.identity))).twice pa
  have eq i : ruler ((s i).tab (x i))=tally (s i).count := by simp [ruler,tally]
  have d : Carries V K (stackRun s (fun i _=>A i)) := by
    apply spread s _
    · simp_rw [eq] at U; exact U
    refine ⟨l,fun i=> ?_⟩
    calc
     _ ≤ ((s i).count+1:ℝ)*((l:ℝ)*W i) := by gcongr; change (size (a i):ℝ)≤ (l:ℝ)*((w i:ℝ)+1); exact_mod_cast e i
     _ = (l:ℝ)*(((s i).count+1)*W i) := by ring
     _ ≤ _ := by gcongr; exact law i
  have M := Strip.coalesce s (fun i y=>send (x i y)) (fun i _=>send (a i)) (show Carries V K _ from pt) d
  have q₁ := liftoff s (fun i y=>Tree.fork (send (x i y)) (A i)) (fun i y=> send (q i (x i y,a i))) (fun i=> W i*f i) h
  exact M.chain (q₁.larger (d:=V) (fun i=> by
    have : 1≤ W i*f i := one_le_mul_of_one_le_of_one_le (s0 i) (b i)
    unfold V; nlinarith [(s0 i)]))
end simple

variable (s:(i:I)→Series (A i)) (t:(i:I)→Series (C i))
variable (x:(i:I)→A i→C i→Y) (b:(i:I)→A i→X)
variable (P:I→Tree) (u : Rip r (fun i=>(s i).count) k P (cloth s t x))
    (v : Rip r (fun i=>(s i).count) k P (stackRun s fun i a=> send (b i a)))
variable (q:(i:I)→ Y×X → Z)
variable (c r₀:ℕ) (d : ∀ i a,size (b i a) ≤ c*(w i+1)) (h : ∀ i a y,size (x i a y) ≤ r₀*(w i+1))
variable (e : ∀ i,((t i).count+1)*(w i+1) ≤ k i+1)
    (F : ∀ i,1≤f i)
    (H : Carries (fun i: Sigma (fun i=>A i × C i)=> ((w i.1:ℝ)+1)*f i.1)
        (fun i=> send (x i.1 i.2.1 i.2.2,b i.1 i.2.1))
        (fun i=> send (q i.1 (x i.1 i.2.1 i.2.2,b i.1 i.2.1))))
    (j : ∀ i,1≤(s i).count)
include u v d h e F H j
theorem paid :
    Breeze f r (fun i=>(s i).count) k P (cloth s t fun i a c=> q i (x i a c,b i a)) := by
  obtain ⟨y,w0⟩ := Rip.coalesce (fun i a=> send (b i a)) (fun i a=> strip (t i) (x i a)) v u
  let Q := Sigma A; let _x (i:Q):=i.1
  let V (i:Q) := t (_x i)
  have U :=
    weight V (fun i=> x i.1 i.2) (fun i=>b i.1 i.2) (q ∘ _x)
      (c:=⟨r₀,fun i j=>h _ _ _⟩) -- name?
      (w:=w ∘ _x) (f:=f ∘ _x) (e:=⟨c,fun i=> d _ _⟩)
      (H.slide (fun (g:Sigma fun i:Sigma A=> C i.fst)=>⟨g.1.1,g.1.2,g.2⟩))
      (fun i=>F (_x i))
  let n i:= (s i).count
  let W i := ((t i).count+1:ℝ)*((w i:ℝ)+1)*f i
  have S := liftoff s (fun i a=> Tree.fork (send (b i a)) (strip (t i) (x i a)))
    (fun i a=> strip (t i) (fun c=> q i (x i a c,b i a))) W U
  let K i:=mass r n k y i
  let ω i:=runrate f r n k y i
  have k₁ i : (n i:ℝ)*((k i:ℝ)+1) ≤ K i := by unfold K mass; gcongr; exact one_le_pow₀ (by simp)
  have k₂ i : 1≤K i := unit_mass j y i
  have κ i : K i≤ ω i := le_mul_of_one_le_right (le_trans (by norm_num) (k₂ i)) (F i)
  refine ⟨F,y,(w0.larger (d:=ω) κ).chain (S.times (fun i=> (k₂ i).trans (κ i)) 2 ?_)⟩
  intro i
  have g : ((t i).count+1:ℝ)*((w i:ℝ)+1) ≤ (k i)+1 := by exact_mod_cast e i
  have y0 := (k₂ i).trans (κ i)
  norm_num
  apply add_le_add _ y0 |>.trans (by linarith : ω i + ω i ≤ 2*ω i)
  unfold W; change (n i : ℝ) * _ ≤ _
  calc
   _ = (n i:ℝ)*(((t i).count+1)*((w i:ℝ)+1))*f i := by ring
   _ ≤ (n i:ℝ)*((k i:ℝ)+1)*f i := by gcongr; linarith [F i]
   _ ≤ _ := mul_le_mul_of_nonneg_right (k₁ _) (by linarith [F i])

end Ask

end IntegerMultiplication
end Computability
end OAI
