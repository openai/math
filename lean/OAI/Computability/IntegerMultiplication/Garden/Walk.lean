import OAI.Computability.IntegerMultiplication.Garden.Ground

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Garden
open Code Brief Grid Staff
open Finset
variable {n : ℕ}
abbrev Notes n:=(Fin n→ℤ)×ℤ
structure Scene (n:ℕ) where
  square : Fin n→Fin n→ℤ
  ray : Fin n→ℤ
  end_ : ℤ

def act (x:Scene n) (p:Notes n) : Notes n :=
  (fun i=> (x.ray i)*p.2+(∑ j : Fin n,x.square i j*p.1 j),
    x.end_*p.2)
-- fits code
structure Lines (x:List S) (f:Fin n→ℤ) : Prop where
  issued : ∃ v:Fin n→S, x=List.ofFn v ∧ ∀ i,whole (v i)=f i
structure frame (x:F) (p:Notes n) : Prop where
  l_ : Lines x.1 p.1
  verify : whole x.2=p.2
structure shown (p:Plan) (x:Scene n) (k:ℕ) : Prop where
  stack : ∃ f:Fin n→Brick,p.1= List.ofFn f ∧
    (∀ i, Lines (f i).2 (x.square i)) ∧ ∀ i,whole (f i).1=x.ray i
  end_ : whole p.2.1 = x.end_
  serial : p.2.2=tally k

private theorem lockS (f g:Fin n→S) :
    lock times Z0 Z0 (List.ofFn f,List.ofFn g)=List.ofFn (fun i=> times (f i,g i)) := by
  let V:=List.ofFn id (n:=n)
  have e (g : Fin n→S) : List.ofFn g = V.map g := by simp [V,List.map_ofFn]
  have t:= fair f g V Z0 Z0
  rw [lock,e f,e g,t]
  unfold V; rw [List.map_map,List.map_ofFn]; rfl
private theorem dotS (f g:Fin n→S) :
    whole (dot (List.ofFn f,List.ofFn g))=∑ i:Fin n,whole (f i)*whole (g i) := by
  rw [dot,waveV,lockS,List.map_ofFn,Signed.summing]
  simp only [Function.comp_def,timeV]
private theorem fireValue {p a:ℤ} (u v:Fin n→ℤ) {p0:S} {z:F} {l:List S}
    (i : Lines l u) (h : Lines z.1 v)
    (q : whole p0=p) (s : whole z.2=a) :
    whole (fire (z,p0,l))=p*a+∑ j:Fin n,u j*v j := by
  obtain ⟨f,t,x⟩:=i.issued
  obtain ⟨g,r,y⟩:=h.issued
  simp only [fire,plus_v,timeV,q,s]
  simp only [t,r,dotS,x,y]

def trim (k:ℕ) (x:Notes n) : Prop :=
  (∀ i,(x.1 i).natAbs < 2^k) ∧ (x.2).natAbs < 2^k
theorem glow {p:Plan} {x:Scene n} {k} (h:shown p x k)
    {v:F} {q: Notes n} (t:frame v q) (e : trim k (act x q)):
    frame (light (p,v)) (act x q) := by
  obtain ⟨⟨f,v_,Q,Y⟩,a,b⟩ := h
  obtain ⟨j,s⟩ := t
  unfold light
  dsimp only
  rw [b,v_]; unfold polyPush; dsimp only; rw [List.map_ofFn,List.map_ofFn]
  refine ⟨⟨fun i=> _,rfl,fun i=> ?_⟩,?_⟩
  · dsimp only [Function.comp_apply]
    have eq i : whole (fire (v,f i))= (act x q).1 i :=
      fireValue (x.square i) q.1 (Q i) j (Y i) s
    rw [t_small,eq]
    rw [eq]; exact e.1 i
  dsimp only
  rw [t_small,timeV,s,a]; rfl
  rw [timeV,a,s]
  exact e.2

-- iteration
theorem imprint {p:Plan} {x:Scene n} {k} (h:shown p x k)
    {v:F} {q:Notes n} (t:frame v q) (m:ℕ)
    (e: ∀ i < m,trim k ((act x)^[i+1] q)) :
    frame (orbit (tally m,p,v)) ((act x)^[m] q) := by
  induction m with
  | zero=> exact t
  | succ m ih=>
    have tc := ih (fun i h=>e i (by omega))
    unfold orbit at *
    dsimp only at *
    rw [tally_length] at tc ⊢
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    exact glow h tc (by simpa [Function.iterate_succ_apply'] using (e m (by omega)))
end Garden

end IntegerMultiplication
end Computability
end OAI
