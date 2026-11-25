import OAI.Computability.IntegerMultiplication.Phase.Guild

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Strip Code Loom
variable {I J : Type} {m : I→ℝ} {r : Regime I} {n l : I→ℕ}
variable {j : Job J} {y : I→J→Prop} {a b : ℤ} {p u v q : I→Tree}
structure Year (j : Job J) (m : I→ℝ) (r : Regime I) (n l : I→ℕ)
    (zone : I→J→Prop) (h : ℤ) (inlet outlet : I→Tree) : Prop where
  safer : ∀ i,1≤ m i
  keys : ∃ k : ℕ,∃ uses : I → List J,
    (∀ i,∀ x∈uses i,zone i x) ∧ (∀ i,(uses i).length≤h) ∧
      ∀ z,Tunnel ⟨z,j.issue,j.reply⟩ (runrate m r n l k) uses inlet outlet

namespace Year

theorem open_ (t : Breeze m r n l p u) :
    Year j m r n l y 0 p u := by
  obtain ⟨d,k,g⟩ := t
  exact ⟨d,k,fun _=>[],by simp,by simp,fun _=> Code.Tunnel.walkway g.runs⟩
theorem fr (t : Rip r n l p u) (h : ∀ i,1≤ m i) :
    Year j m r n l y 0 p u :=
  open_ (Breeze.launch t h)
theorem extend (t : Year j m r n l y a p u) (e : Year j m r n l y b u q) :
    Year j m r n l y (a+b) p q := by
  obtain ⟨d,k,z,v,T,S⟩ := t
  obtain ⟨_,h,w,x,U,P⟩ := e
  refine ⟨d,k+h,fun i=> z i++w i,fun i j m => ?_,fun _=>?_, fun Z=>?_⟩
  · cases List.mem_append.mp m with
    | inl a => exact v i j a
    | inr b => exact x i j b
  · dsimp only; rw [List.length_append]; push_cast; exact add_le_add (T _) (U _)
  exact (Loom.Tunnel.monoT (S Z) (fun i=>rate_higher i (d i) (by omega : k ≤ k+h))).join
    (Loom.Tunnel.monoT (P Z) (fun i=>rate_higher i (d i) (by omega : h ≤ k+h)))

theorem relax (t : Year j m r n l y a p u) (e : a≤b) :
    Year j m r n l y b p u := by
  obtain ⟨d,k,w,z,x,h⟩ := t
  exact ⟨d,k,w,z,fun _=> (x _).trans e,h⟩
theorem strap (t : Year j m r n l y a p u) (v : I → Tree) :
    Year j m r n l y a (together p v) (together u v) := by
  obtain ⟨d,k,w,z,x,h⟩ := t
  exact ⟨d,k,w,z,x,fun Z=>(h Z).surround v⟩
theorem call (h : ∀ i,1≤ m i) (u : I→J)
    (zone : ∀ i,y i (u i)) (z : ∀ i,1≤n i) :
    Year j m r n l y 1 (j.issue ∘ u) (j.reply ∘ u) := by
  have e i : 1≤ runrate m r n l 0 i :=
    one_le_mul_of_one_le_of_one_le (unit_mass z _ i) (h i)
  exact ⟨h,0,fun i=>[u i],by simpa using zone,by simp,fun _=>Code.Tunnel.summon u e⟩
theorem openFirst (t : Year j m r n l y a p u)
    (h : Rip r n l v p) :
    Year j m r n l y a v u := by simpa only [zero_add] using (fr h t.safer).extend t
theorem openLast (t : Year j m r n l y a p u)
    (h : Rip r n l u v) :
    Year j m r n l y a p v := by simpa only [add_zero] using t.extend (fr h t.safer)

theorem splitPath (U : Year j m r n l y a p u) (V : Year j m r n l y b p v)
    (H : Alive r n l p) (A : Alive r n l u) (B : Alive r n l v) :
    Year j m r n l y (a+b) p (together u v) := by
  have sweep (p q : I → Tree) (hp : Alive r n l p) (hz : Alive r n l q) :
      Rip r n l (together p q) (together q p) :=
    (Rip.split (Rip.alivePair hp hz)).2.twice (Rip.split (Rip.alivePair hp hz)).1
  exact ((((U.strap p).openLast (sweep u p A H)).extend
    (V.strap u)).openLast (sweep v u B A)).openFirst (H.twice H)
variable {W : Type} [Fintype W]
theorem static (s : Series W) (b : W → ℤ) (v : I → W→Tree)
    (f : ∀ w,Year j m r n l y (b w) p (fun i=> v i w))
    (H : ∀ i,1≤ m i) (z : Alive r n l p)
    (a : ∀ w,Alive r n l (fun i => v i w))
    (_hn : ∀ i,1≤n i) :
    Year j m r n l y (∑ w:W,b w) p (stackRun (fun _=>s) v) := by
  classical
  unfold stackRun
  simp_rw [stripe_simple]
  have w : s.explore.toFinset=Finset.univ := by ext; simp [s.complete]
  rw [← w]
  suffices t : ∀ (U : List W),U.Nodup→
      Alive r n l (fun i=> Task.forest (v i) U) ∧
      Year j m r n l y (U.toFinset.sum b) p (fun i=>Task.forest (v i) U) from (t _ s.nodup).2
  intro U e
  induction U with
  | nil =>
    have u : Rip r n l p (fun i => Task.forest (v i) []) := by
      obtain ⟨k,d⟩ := z; exact ⟨k,fixture d.out d.budget _⟩
    exact ⟨u.idle,by simpa using (fr u H : Year j m r n l y 0 _ _)⟩
  | cons w L ih =>
    rw [List.nodup_cons] at e
    obtain ⟨h,d⟩ := ih e.2
    exact ⟨Rip.alivePair (a w) h,by
      simpa only [Task.forest_cons,together,List.toFinset_cons,Finset.sum_insert (show w ∉ L.toFinset by simpa using e.1)] using (f w).splitPath d z (a w) h⟩

end Year

/-- retains header for arrivals -/
abbrev Quarterback (j : Job J) (m : I→ℝ) (r : Regime I) (n l : I→ℕ) (y : I→J→Prop)
    (a : ℤ) (v p : I→Tree) := Year j m r n l y a (together r.header v) p
namespace Quarterback
theorem run (t : Quarterback j m r n l y a p u) (e : Quarterback j m r n l y b u v)
    (h₀ : ∀ i,1 ≤ n i)
    (H : Alive r n l p) (A : Alive r n l u) :
    Quarterback j m r n l y (a+b) p v := by
  let F := Year.fr (j:=j) (y:=y) (Drive.fetch h₀ H) t.safer
  have z : Year j m r n l y a (together r.header p) (together r.header u) := by
    simpa only [zero_add] using (F.splitPath t (Rip.alivePair (Drive.started h₀) H)
      (Drive.started h₀) A)
  exact z.extend e
end Quarterback
end Phase

end IntegerMultiplication
end Computability
end OAI
