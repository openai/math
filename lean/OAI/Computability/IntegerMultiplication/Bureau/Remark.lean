import OAI.Computability.IntegerMultiplication.Bureau.Radar

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Bureau
open Param Scale Brief Carry Strip Code Halo
variable {I:Type} {n:I→ℕ} {p q:I→Tree}
theorem dispatchT (f:I→ℕ)(g:Figure (city n) f)(v:∀ i,f i≤ton n i):
    Carries (token n) (cell n) (fun i=>send (tally (f i))) := by
  obtain ⟨x,e,w⟩:=g
  have t := dispatch e
  obtain ⟨j,E⟩:= t.out
  have d:= rice.on x
  simp only [w] at d
  apply t.sequence
  refine ⟨t.budget,_,d,j+2,fun i=>?_⟩
  have U:(f i:ℝ)≤token n i:=by unfold token; exact_mod_cast v i
  specialize E i
  change (size (x i):ℝ)≤_ at E
  push_cast; linarith [t.budget i]

theorem gig (a b:I→ℕ)(ha:Carries (token n) p (fun i=>send (tally (a i))))
    (hb: Carries (token n) p (fun i=>send (tally (b i))))
    (e : ∀ i,(a i+1)*(b i+1) ≤ 6*ton n i):
    Carries (token n) p (fun i=>send (List.replicate (a i) (tally (b i)))) := by
  let x(i:I):Tally×Tally:=(tally (a i),tally (b i))
  have v:= (generate (X:=Tally)).on x
  have p := ha.twice hb
  apply p.sequence
  unfold x at v
  simp only [tally_length,size_tally] at v
  refine ⟨ha.budget,_,v,15,fun i=>?_⟩
  have E:(a i+1)*size (tally (b i)) ≤ 12*ton n i:=by
    rw [size_tally,tally_length]; specialize e i; nlinarith
  rw [size_tally,tally_length] at E
  unfold token
  norm_cast
  nlinarith [tonp n i]

variable (n)
private theorem traf (h:∀i,Season (n i)):
    Carries (token n) (cell n)
      (fun i=>send (List.replicate (Floorplan (n i)).count (tally (Peace (n i)).count))) := by
  let g:=guide_city n
  let r i:= load (n i)
  let v i:= wall (n i)
  let p i:= (Floorplan (n i)).count
  have V : Figure (city n) r:=(Figure.natural 2).repeated (g.exSize n)
  have W : Figure (city n) v:= g.side_long n
  have k : (p:I→ℕ)=fun i=>r i/v i:=by
    funext i
    have t:1≤v i:=Nat.pow_pos (by decide)
    change _=load _/_
    rw [← metric (h i)]
    unfold v; rw [Nat.mul_div_cancel _ t]
  have P : Figure (city n) p:= (k ▸ (V.quotients W))
  have s i : v i≤ton n i:= by
    have b:=metric (h i)
    unfold v ton
    have c:=place (h i)
    exact le_trans (Nat.le_mul_of_pos_left _ c) (b ▸ Nat.le_mul_of_pos_right _ (budget_p _)) -- orientation?
  have t i : p i≤ton n i :=
    le_trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide) : 0<wall (n i))) (by
      change _*wall (n i)≤_
      rw [metric (h i)]; exact Nat.le_mul_of_pos_right _ (budget_p _))
  simp_rw [tallZ]
  exact gig p v (dispatchT p P t) (dispatchT v W s) (fun i=>by
    unfold ton v p
    have M:=metric (h i)
    have t:1≤wall (n i):=Nat.pow_pos (by decide)
    have u : load (n i) ≤ load (n i)* Scale.P (n i):= Nat.le_mul_of_pos_right _ (budget_p _)
    have b:=place (h i); nlinarith)
variable (h:∀i,Season (n i))(x:(i:I) → Cone.Farm (n i))
abbrev facad (i:I) (j:Floor (n i) × dayV (n i)) :=
  send (coda (n i) (x i) (uX (h i) j.1.1 j.1.2 j.2))
theorem facsim (i:I):
    flat (h i) (x i)=stripe ((Floorplan (n i)).cart (Peace (n i))) (facad n h x i) := by
  unfold flat walk stripe
  rw [Series.tab_via]; rfl
abbrev LandN i:= flat (h i) (x i)
abbrev ExtN i:= singlet (h i) (x i)
theorem grouping :
    Wood n (LandN n h x) (ExtN n h x) := by
  apply rows (fun i=>Floorplan (n i)) (fun i=>Peace (n i)) (facad n h x)
  have k:=sedan n h x
  have z:= ((scoop k).chain (traf n h)).twice (me k)
  unfold together at z
  simp_rw [facsim] at z -- p flat also rewritten
  simp_rw [← facsim]
  simp_rw [← facsim] at z
  exact z
theorem levee :
    Wood n (ExtN n h x) (LandN n h x) := by
  have e:= Strip.flatten (fun i=>Floorplan (n i)) (fun i=>Peace (n i)) (facad n h x) (me (ocean n h x))
  simp_rw [← facsim] at e
  exact e
end Bureau

end IntegerMultiplication
end Computability
end OAI
