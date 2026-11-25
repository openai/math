import OAI.Computability.IntegerMultiplication.Spindle.All

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Spindle
open Strip Dims Loom Code Adic
variable {I J W L X : Type} [DecidableEq J] [Fintype J] [Fintype W]
variable {p : ℕ} [NeZero p] {τ : ℝ} {r : Regime I}
variable (s G B : I→Tape) (t : I→ℕ)
noncomputable section

variable (R : Series W) (d : Design J W L p τ)
abbrev modes := fun i : I => ((t i+1:ℕ):ℝ)^τ
theorem belly (h : 0≤τ) (i:I) : 1 ≤ modes (τ:=τ) t i :=
  Real.one_le_rpow (by push_cast; simp) h
include R d
private theorem bulletin (u : I→List Tally)
    (b : (i:I)→Bounds (dim J) p (u i))
    (l : I→ℕ) (a : I→ℕ) (ha : ∀ i,a i≤l i)
    (v : (i:I)→(b i).sector→Fin (a i)→Bead)
    (H : r.Has (fun i => (b i).mint)) (f : Dom r.scale (fun i => (b i).scale))
    (e : ∀ i j,(u i).count j≤dim J) (h : 0<τ) :
    Breeze (modes (volume (dim J) ∘ u) (τ:=τ))
      r (fun i => (b i).sectorS.count) l (together r.header (cloth (fun i => (b i).sectorS)
        (fun i => Series.natural (a i)) v))
      (cloth (fun i => (b i).sectorS) (fun i => Series.natural (a i)) (fun i => v i ∘ swapper _ _ _)) := by
  let q := modes (volume (dim J) ∘ u) (τ:=τ)
  have v0 := belly (volume (dim J) ∘ u) h.le
  obtain ⟨M,y⟩ := brave h d.occupancy
  let g i : Hull (dim J) p := ⟨_,b i,a i,v i⟩
  obtain ⟨k,A⟩ := campaign R d h
  have z := A.along g
  let T i := (b i).sectorS
  have open0 := Bounds.opened b d.large d.occupancy H f
  let n0 := open0.1
  let n := Hull.rate ∘ g
  let G := regime (p:=p) d.occupancy
  obtain ⟨j,C,vL⟩ := (f.add (Dom.const _ 1)).pow k
  have adapt : Sized (runrate q r n l j)
      ((codeChart ..).issue ∘ g) ((codeChart ..).reply ∘ g) := by
    refine z.adapts (fun i => one_le_mul_of_one_le_of_one_le (unit_mass n0 _ i) (v0 i))
      ((C+1)*M) (fun i => ?_)
    change mass G Hull.rate Hull.width k (g i)*(acres τ (dim J) (u i)+1) ≤ _
    have t' : mass G Hull.rate Hull.width k (g i) ≤ ((C:ℝ)+1)*mass r n l j i := by
      unfold mass G regime Hull.rate Hull.width
      change (n i:ℝ)*((a i:ℝ)+((b i).scale+1:ℝ)^k) ≤ _
      rw [← mul_assoc ((C:ℝ)+1), mul_comm ((C:ℝ)+1) (↑(n i)),mul_assoc]
      gcongr
      -- gcongr skips a if equals l? see
      have hx : ((b i).scale+1:ℝ)^k ≤ (C:ℝ)*(r.scale i+1:ℝ)^j := by exact_mod_cast vL i
      have gA : (a i:ℝ) ≤ l i := by exact_mod_cast ha i
      nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ r.scale i+1) j, Nat.cast_nonneg (α:=ℝ) C,
          Nat.cast_nonneg (α:=ℝ) (l i)]
    calc
     _ ≤ (((C:ℝ)+1)*mass r n l j i)*((M:ℝ)*q i) := by
      apply mul_le_mul t' (y _ (e i))
      · have hx : 0 ≤ acres τ (dim J) (u i) := by
          unfold acres
          apply List.sum_nonneg; intro t h
          obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
          unfold dim; positivity
        linarith
      have hz := unit_mass (r:=r) (l:=l) n0 j i
      exact mul_nonneg (by positivity) (le_trans (by norm_num) hz)
     _ = _ := by unfold runrate; push_cast; ring
  let hv := cloth_size T (fun i => Series.natural (a i)) open0 v (fun i => by simpa using ha i)
  have prep := ((Drive.fetch n0 hv).chain (Rip.header n0 H)).twice (Drive.self n0 hv)
  obtain ⟨y,x⟩ := prep
  have c := x.larger (fun i => (mass_le (r:=r) (l:=l) (by omega : y≤y+j) i).trans
    (le_mul_of_one_le_right (by unfold mass; positivity) (v0 i)))
  exact ⟨v0,y+j,c.sequence (adapt.mono (fun i => rate_higher i (v0 i) (by omega)))⟩
-- controller generic
theorem orbitalFin (h : 0<τ)
    (guard : ∀ i n,n∈s i ++ G i ++ B i → 2≤n ∧ n≤p)
    (S : r.Has (shape ∘ s)) (Y : r.Has (shape ∘ G)) (Z : r.Has (shape ∘ B))
    (h0 : r.Has (tally ∘ t)) (l : I→ℕ) (a : I→ℕ) (ha : ∀ i,a i≤l i)
    (v : (i:I) → SpanKey (s i) (G i) (B i) (Block p (t i)) → Fin (a i)→Bead) :
    Breeze (modes t (τ:=τ)) r (fun i => (stock p (s i) (G i) (B i) (t i)).count) l
      (together r.header (cloth (fun i => stock p (s i) (G i) (B i) (t i)) (fun i => Series.natural (a i)) v))
      (cloth (fun i => stock p (s i) (G i) (B i) (t i)) (fun i => Series.natural (a i)) (fun i => v i ∘ swapper _ _ _)) := by
  let u i := Code.hashPlan (dim J) d.occupancy (Code.tally (t i))
  let P i := volume (dim J) (u i)
  have e (i:I) : P i=t i := by simpa only [P,u,tally_length] using
    (Code.safePlan (dim J) d.occupancy (Code.tally (t i))).1
  let b (i:I) : Bounds (dim J) p (u i) :=
    ⟨(s i).length+(G i).length+(B i).length+2*P i,s i,G i,B i,guard i, le_rfl⟩
  have j : r.Has (fun i => (b i).mint) :=
    (h0.thenDo (Code.poly_plan _ _)).pair (S.pair (Y.pair Z))
  have vt : Dom r.scale t := (Regime.Small.extent (r:=r) (k:=fun i => send (tally (t i))) h0).mono
    (fun i => by change _ ≤ size (tally (t i)); rw [size_tally,tally_length]; omega)
  have y {s : I→Tape} (h : r.Has (shape ∘ s)) :
      Dom r.scale (fun i => (s i).length) := by
    apply (Regime.Small.extent h).mono
    intro i; change _ ≤ size (shape _)
    generalize s i=b
    induction b with
    | nil => simp
    | cons i b ih => simp only [List.length_cons,shape_cons,size_cons]; omega
  have ge : Dom r.scale (fun i => (b i).scale) := by
    change Dom r.scale (fun i => _+_+_+2*P i)
    simpa only [e] using (((y S).add (y Y)).add (y Z)).add ((Dom.const _ 2).mul
      (show Dom r.scale P by simpa only [Dom,e] using vt)) -- maybe
  suffices H : ∀ v : (i:I) → SpanKey (s i) (G i) (B i) (Block p (P i)) → Fin (a i) → Bead,
      Breeze (modes P (τ:=τ)) r (fun i => (stock p (s i) (G i) (B i) (P i)).count) l
      (together r.header (cloth (fun i => stock p (s i) (G i) (B i) (P i)) (fun i => Series.natural (a i)) v))
      (cloth (fun i => stock p (s i) (G i) (B i) (P i)) (fun i => Series.natural (a i))
        (fun i => v i ∘ swapper _ _ _)) by
    rw [funext e] at H
    exact H _
  intro v
  exact bulletin R d u b l a ha v j ge (fun i m =>
    ((Code.safePlan (dim J) d.occupancy _).2 m).le) h
end
end Spindle

end IntegerMultiplication
end Computability
end OAI
