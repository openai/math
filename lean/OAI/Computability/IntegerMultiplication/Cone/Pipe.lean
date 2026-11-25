import OAI.Computability.IntegerMultiplication.Cone.Brigade

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Cone
open Echo Scale IntegerMultiplication.Fourier Cap Param
variable {n:ℕ} (spark:Season n)
-- pending FFT source simulation interface, easy algebra bounds
noncomputable section
structure Organ (n:ℕ) where
  rite : Bool→Farm n→Farm n
structure Angled (n) (x:Organ n):Prop where
  norms B u f (v:1≤B)(w:B≤ hi n 700)(t:Bound (array_ n f) B):
    Bound (array_ n (x.rite u f)) (B*hi n 16)
  error B u f (v:1≤B)(w:B≤ hi n 700)(t:Bound (array_ n f) B):
    Gap (array_ n (x.rite u f)) (strand (criterion n) (Echo.Mounting n u) (array_ n f)) (err n*hi n 32*B)

include spark
theorem mMount (u:Bool){x y:Land n}{B:ℝ}(t:0≤B)(e:Gap x y B):
    Gap (strand (criterion n) (Mounting n u) x) (strand (criterion n) (Mounting n u) y)
      (hi n 1 *B) := by
  change Bound (strand (criterion n) (Mounting n u) x-strand (criterion n) (Mounting n u) y) _
  rw [← Echo.strand_sub]
  exact (Echo.phaseMeasure _ (fun i=>bif u then (modulus n i :ℤ) else -(modulus n i:ℤ)) (x:=x-y) t e).mono
    (by gcongr; exact read_r spark)

omit spark
variable {I:Type} (r:I→ℕ) (z:Faculty r) (v:I) (h : Season (r v)) (t:z.quality r)
abbrev enlarged : Plans (r v):= fun i=> extend_ r z v h i
abbrev settled (u:Bool) : Plans (r v):= fun i=> close_ r z v h i u
def ray (x:Organ (r v)) (u:Bool) : Farm (r v)→Farm (r v) :=
  let m:=Measure (lanes (r v))
  (brisk (r v) (settled r z v h u) m) ∘ x.rite u ∘
    brisk (r v) (enlarged r z v h) m

/-- Shaped local bounds for any fixed complex array operator. Relative uniform. -/
structure Flow {n} (m k l : ℕ) (X : Farm n→Farm n)
    (T:Land n→Land n) : Prop where
  norm_ (B:ℝ) (u:1≤B) (v:B≤hi n m)(x:Farm n)(t:Bound (array_ n x) B):
    Bound (array_ n (X x)) (B*hi n k)
  delta (B:ℝ)(u:1≤B)(v:B≤hi n m)(x:Farm n)(t:Bound (array_ n x) B):
    Gap (array_ n (X x)) (T (array_ n x)) (err n*B*hi n l)
  normal (B:ℝ)(u:0≤B)(x y:Land n)(t:Gap x y B):
    Gap (T x) (T y) (B * hi n k)
-- composition
theorem Flow.chain {p k l a b c:ℕ} {x y:Farm n→Farm n}
    {u v:Land n→ Land n} (T:Flow p k l x u) (Q:Flow a b c y v)
    (P0:ℕ) (h:P0≤p) (H:P0+k ≤ a) :
    Flow P0 (k+b) (l+c+k+b+1) (y ∘ x) (v ∘ u) where
  norm_ B r j f t := by
    let z:= hi n
    have e (b):= hi1 n b
    have I:= T.norm_ B r (j.trans (hi_mono _ h)) f t
    have D:B*hi n k≤hi n a := ((mul_le_mul_of_nonneg_right j (by linarith [e k])).trans (heightA n P0 k).le).trans (hi_mono _ H)
    have G:= Q.norm_ _ (one_le_mul_of_one_le_of_one_le r (e _)) D _ I
    exact G.mono (le_of_eq (by rw [← heightA,mul_assoc]))
  delta B r j f t := by
    let z:= hi n
    have e (b):= hi1 n b
    have I:= T.norm_ B r (j.trans (hi_mono _ h)) f t
    have D:B*hi n k≤hi n a := ((mul_le_mul_of_nonneg_right j (by linarith [e k])).trans (heightA n P0 k).le).trans (hi_mono _ H)
    have G:= Q.delta _ (one_le_mul_of_one_le_of_one_le r (e _)) D _ I
    have E:= T.delta B r (j.trans (hi_mono _ h)) f t
    have e0:= invp n
    have w : 0 ≤ err n * B * hi n l := by have := e l; positivity
    have K:= Q.normal _ w _ _ E
    apply (G.trans K).mono
    rw [show err n*(B* hi n k)*hi n c + err n*B*hi n l*hi n b=err n*B*(hi n k*hi n c+hi n l*hi n b) by ring, heightA,heightA]
    gcongr
    have t1:=hi_mono n (by omega : k+c≤l+c+k+b)
    have t2:=hi_mono n (by omega : l+b≤l+c+k+b)
    exact le_trans (add_le_add t1 t2) (by linarith [overhead (l+c+k+b) n])
  normal B r f g t := by
    have i:=T.normal _ r f g t
    have j : 0≤ B*hi n k := by have := hi1 n k; positivity
    have p:= Q.normal _ j _ _ i
    rw [mul_assoc,heightA] at p; exact p
private theorem seqFlow (k : Square (criterion n))(p:Plans n)
    (H:∀i,Row (k i) (p i)):
    Flow 750 26 27 (brisk n p (Measure (lanes n))) (strand (criterion n) k) where
  norm_ B u v x t:= (release k p H x u v t).1
  delta B u v x t:= (release k p H x u v t).2.mono (le_of_eq (by ring))
  normal B u x y t:= by
    let M:=Measure (lanes n)
    have E:=assured k p H x y M u t
    dsimp only at E
    have Z:=measure_specs (lanes n)
    rw [Echo.schedule k _ _ Z.2.1 Z.2.2, Echo.schedule k _ _ Z.2.1 Z.2.2] at E
    unfold M at E; rw [Z.1] at E
    exact E.mono (mul_le_mul_of_nonneg_left (flareBound n) u)

include h
private theorem angleFlow {x:Organ (r v)} (q:Angled _ x) (i:Bool):
    Flow 700 16 32 (x.rite i) (strand (criterion (r v)) (Mounting (r v) i)) where
  norm_ _ _ _ _ _:= q.norms _ _ _ (by assumption) (by assumption) (by assumption)
  delta _ u v x t:=(q.error _ _ x u v t).mono (le_of_eq (by ring))
  normal B u x y t:= (mMount h _ u t).mono (by rw [mul_comm]; gcongr; exact hi_mono _ (by decide:1≤16))

include t
theorem travel (x:Organ (r v))(w:Angled (r v) x)(i:Bool):
    Flow 500 68 198 (ray r z v h x i) (desired h i) := by
  let N:=r v; let q:=hi N
  have A:=seqFlow (n:=N) (Growing N h) (enlarged r z v h) (a_rule r z t v h)
  have B:=seqFlow (n:=N) (Closing N i h) (settled r z v h i) (fun j=>b_rule r z t v h j i)
  have C:=(angleFlow r v h w i).chain B 700 (by decide) (by decide)
  have Q:= A.chain C 500 (by decide) (by decide)
  change Flow 500 68 _ (ray r z v h x i) (desired h i) at Q
  -- 32+27+16+26+1=102; 27+102+26+42+1=198
  exact Q
end
end Cone

end IntegerMultiplication
end Computability
end OAI
