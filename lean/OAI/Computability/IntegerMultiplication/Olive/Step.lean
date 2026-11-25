import OAI.Computability.IntegerMultiplication.Olive.Static

namespace OAI
namespace Computability
namespace IntegerMultiplication

set_option maxHeartbeats 400000
namespace Olive
open Well Larch Bureau Halo Moira Param Scale Strip Dims Code
open Rivulet Dusk Grid Echo Cone Cap Brief Staff
variable {I:Type}(n:I→ℕ){r:Regime I}(T:Origin n r)(h:(i:I)→Season (n i))(a:(i:I)→Direction (n i))(A:Realizes r (fun i=> (a i).val))
variable (σ:(i:I)→Fin (axio n a i)→Fin (axio n a i))
variable (b:(i:I)→Fin (axio n a i)→ Cone.G (n i))
variable (m:I→Rivulet.Menu) (f:List Morse.Seat × Rivulet.Menu→ List Morse.Seat)
variable (C:Standards n a σ b m f r)

noncomputable section
-- registered packet format correspondence
variable (x:(i:I)→Farm (n i))
abbrev loc_ i l y z :=
  x i (memo n h a i l y z)
abbrev bill i l j := (rightG n h a i).tab (fun v=>Dusk.mark (loc_ n h a x i l j v))
abbrev play i l:= send ((List.ofFn (bill n h a x i l)))
abbrev charter (x:(i:I)→Farm (n i))(i:I):= send ∘ Halo.coda (n i) (x i)
theorem spine: bearing n h a (charter n x) = stackRun (leftG n h a) (play n h a x) := by
  unfold stackRun bearing triple play
  funext i; apply congrArg (stripe (leftG n h a i)); funext z
  let t:=turnG n a i
  let q:=rightG n h a i
  let L:= bill n h a x i z
  change stripe t (fun j=>stripe q (fun p=>send (Dusk.mark (loc_ n h a x i z j p)))) = send (List.ofFn L)
  have e(j:M n a i):
      stripe q (fun p=> send (Dusk.mark (loc_ n h a x i z j p)))=send (L j):=stripe_eq' ..
  simp_rw [e,stripe_eq']
  change send (List.map L (List.finRange _))=_
  simp [List.finRange,Function.comp_def]

-- term specification
abbrev give (i:I)(g:Fin (axio n a i)→ Cone.G (n i)) (j):=
  Cone.punch (g (σ i j)) (b i j)
abbrev grow (i:I) := Echo.street (a i) (give n a σ b i) (x i)
theorem grow_r (i:I)(l)(j:M n a i)(p):
    loc_ n h a (grow n a σ b x) i l j p=
      punch (loc_ n h a x i l (σ i j) p) (b i j):= by
  change give n a σ b i (fun t=> x i (Echo.alter (memo n h a i l j p) (a i) t)) ((memo n h a i l j p) (a i)) = _
  rw [consistent,give,covering]

include T A C
-- dossier per pass .compute. movement via Story transformation.
theorem lesson :
    Mid n r (boundG n) (LandN n h x) (LandN n h (grow n a σ b x)) := by
  let y:=grow n a σ b x
  have hX:= brief n T h a A (charter n x) (sedan n h x)
  have W:=weather n T h a A σ b m f C (sedan n h x)
  let d:Cue:=([],[],[])
  let φ:Story→ List Rivulet.Note:=fun q=> lock id ([]:Morse.Seat) d (f (q.1,q.2.1),q.2.2)
  have P:Easy φ := by unfold φ; have z:=C.proc; have j:=easy_lock id Easy.identity ([]:Morse.Seat) d; fun_prop
  let z:=leftG n h a
  let p:=LandN n h x
  rw [spine] at hX
  let ψ (i:I)(q:L n h a i):Story:=(List.ofFn (bill n h a x i q), wages n a b m i)
  have S : Mix n r p (stackRun z (fun i p=>send (ψ i p))) :=
    Strip.coalesce z _ _ hX W -- typo
  have Q : Mix n r p (send ∘ (fun i=> (z i).tab (ψ i))):=by
    unfold stackRun at S
    simp_rw [stripe_eq'] at S; exact S
  have E:= Q.chain (Carries.func Q.budget Q.out (List.map φ) P.mapping)
  let Y(i:I):= turnG n a i
  let X (i:I)(a0:L n h a i)(j:M n a i): Rivulet.Note := (bill n h a x i a0 (σ i j),coupon n a b i j)
  have eN {X:Type}{i:I}(f:Fin (axio n a i)→X):
      List.ofFn f=(Y i).tab f:= by change List.ofFn f=List.map _ (List.finRange _); simp [List.finRange,Function.comp_def]
  have e (i:I)(a0:L n h a i): φ (ψ i a0) =(Y i).tab (fun j=>X i a0 j) := by
    unfold φ ψ; change lock _ _ _ (f (_,m i),List.ofFn _)=_
    rw [C.tells,eN,eN,paired];rfl
  have eq :
      (fun i=> send (List.map φ ((z i).tab (ψ i))))=
        stackRun z (fun i a=>stripe (Y i) (fun j=> send (X i a j))) := by
    unfold stackRun; simp_rw [Series.map_tab,Function.comp_def,e,stripe_eq']
  change Mix n r p (fun i=> send (List.map φ ((z i).tab (ψ i)))) at E
  rw [eq] at E
  -- apply purse pointwise where i:Sigma × i-prefix × axio.
  let R := fun i=> L n h a i × M n a i
  let root(s:Sigma R):=s.1
  let Z(s:Sigma R):=rightG n h a s.1
  let w:=Scale.W ∘ n
  let k:=Scale.F ∘ n
  let b0(s:Sigma R):=b s.1 s.2.2
  let t0(s:Sigma R)(v:U n h a s.1):=loc_ n h a x s.1 s.2.1 (σ s.1 s.2.2) v
  let lab(i:I):=Moira.land z Y i
  let V(i:I):ℝ:=((rightG n h a i).count+1:ℝ)* Grid.cost w i
  let o(i:I)(p:L n h a i)(j:M n a i):=
    stripe (rightG n h a i) (fun v=>send (Dusk.mark (loc_ n h a y i p j v)))
  let P0(i:I)(s:R i):=send (X i s.1 s.2)
  have F:Carries (V ∘ (Sigma.fst:Sigma R→I)) (fun s:Sigma R=>P0 s.1 s.2) (fun s:Sigma R=>o s.1 s.2.1 s.2.2):= by
    have T:= purse Z (w ∘ root) (k ∘ root) t0 b0 (by
      intro s; change Scale.F _≤ Scale.W _+1; unfold Scale.F Scale.W; omega)
    unfold o y; simp_rw [stripe_eq', grow_r] -- grow unfolded prevents rewrite, unfold only y
    exact T
  have d1:= liftoff lab P0 (fun i s=>o i s.1 s.2) V F
  have G0(i:I):1≤ boundG n i:=by exact_mod_cast tax_pos ..
  let t:=grant n (boundG n)
  have v₁ (i:I): ((lab i).count:ℝ)*V i+1≤ 20000*t i := by
    let N:= Scale.W (n i)+1
    let B:ℕ:=ct z i*axio n a i
    let J:=ct (suffixL n h a) i
    have JT:(lab i).count=B:=by unfold lab land Y turnG mid_ B; simp only [Series.count_cart, Series.count_natural]
    rw [JT]; unfold V Grid.cost; change (B:ℝ)*((J+1)*((w i+1)*(boundG n i)))+1≤_
    have c:1≤J:= (passport n h a).p i
    have A :=IntegerMultiplication.Well.volume n h a i
    have q:(B:ℝ)*(J+1)*N≤ 2*8193*token n i:= by
      unfold token; exact_mod_cast (show B*(J+1)*N≤ 2*8193*ton n i from
        le_trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega : J+1≤2*J)) (near_ _)) (by
          have e:B*J=load (n i):= A
          unfold ton; nlinarith))
    have K:=mul_le_mul_of_nonneg_right q (by linarith [G0 i]:0≤ boundG n i)
    have L:= mint_ n G0 i
    unfold N at K; push_cast at K ⊢
    unfold t grant w
    dsimp only [Function.comp_apply]; unfold grant at L
    nlinarith
  have D1 :Mid n r (boundG n) p (stackRun lab P0) :=
    Strip.flatten z Y (fun i (p:R i)=>P0 i p)
    (IntegerMultiplication.Well.launch G0 E)
  have H1:=D1.chain (d1.times D1.budget 20000 (fun i=>v₁ i))
  -- result upper rows = convert via flatten direct. raw s.
  let C0 (i:I) (p:R i) (t:U n h a i):= fctor n h a (charter n y) i p.1 p.2 t
  have U0:= Strip.flatten lab (rightG n h a) (fun i (w:R i×U n h a i)=>C0 i w.1 w.2) H1
  change Mid n r (boundG n) p (raw (prefixL n h a) (mid_ n a) (suffixL n h a) (fctor n h a (charter n y))) at U0
  rw [faith] at U0
  exact U0
end
end Olive

end IntegerMultiplication
end Computability
end OAI
