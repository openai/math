import OAI.Computability.IntegerMultiplication.Packed.Fore

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Packed
open Strip Code Loom Adic Port Dims
noncomputable section
private theorem lineShift {H L i} (o : Packed.Span ℤ i) (z : Block 2 (cap i H L)) :
    (slide (H:=H) (L:=L) o).symm ((package H L i).cast.symm z) =
      (package H L i).cast.symm ((glide (offsets (H:=H) (L:=L) o)).symm z) := by
  apply plane.injective
  have hp z : plane ((package H L i).cast.symm z) = Adic.index 2 (cap i H L) z := by
    change Adic.index _ _ ((package H L i).cast _)=_
    exact congrArg (index 2 _) ((package H L i).cast.apply_symm_apply _)
  rw [hp, slide,Equiv.symm_trans_apply,Equiv.symm_trans_apply,Equiv.symm_symm,Equiv.apply_symm_apply,hp]
  let v := offsets (H:=H) (L:=L) o
  let r' := (glide v).symm z
  have h : Adic.index 2 (cap i H L) z=Adic.index 2 (cap i H L) r' + v := by
    simpa only [r',Equiv.apply_symm_apply] using move_nat v r'
  change Adic.index 2 (cap i H L) z + -v=Adic.index 2 _ r'
  rw [h,add_assoc,add_neg_cancel,add_zero]
variable {X : Type} (P G R S : X→Tape) (H L i : X→ℕ) {r : Regime X}
variable (hP : Told r P) (hG : Told r G) (hR : Told r R) (hS : Told r S)
variable (h : r.Has fun x => tally (cap (i x) (H x) (L x)))
variable (D : r.Has fun x => signs (H x) (L x) (i x))
-- control based translation
abbrev eyeAt {P0 G0 R0 : Tape} {K : Type} (q : Pos) (v : fore P0 G0 R0 K) :=
  if q=Pos.sun then (eye v).1 else (eye v).2
private theorem note0 {P0 G0 R0 S0 : Tape} {K : Type}
    (q : Pos) (v : Dome P0 G0 R0 S0 K) (t:q≠.moon) :
    indexOf q v = eyeAt q (fors v) := by cases q <;> first | rfl | contradiction
-- Standalone address lemma, without family metavariables
abbrev blend (P G R S : Tape) {h1 l j : ℕ} (x : fore P G R (Queue h1 l j))
    (b0 : Block 2 (cap j h1 l) × Pin S) :
    Dome P G R S (Queue h1 l j) :=
  (x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2,(package h1 l j).cast.symm b0.1,b0.2)
abbrev prefixO {P' G' R' : Tape} {H' L' i' : ℕ}
    (t : Turn) (q : Equiv.Perm Pos) (u:fore P' G' R' (Queue H' L' i')) :=
  start t (eyeAt (q .sun) u) (eyeAt (q (remote t)) u)
private theorem focusO {P1 G1 R1 S1 : Tape} {k j i:ℕ}
    (x:fore P1 G1 R1 (Queue k j i)) (b:Block 2 (cap i k j) × Pin S1) (t : Turn)
    (q : Pos≃Pos) (e : q (target t)=.moon) :
    (invoke (agent q (walk t)) _ _ _ _).symm (blend _ _ _ _ x b)=
      blend _ _ _ _ x ((glide (offsets (H:=k) (L:=j) (prefixO t q x))).symm b.1,b.2) := by
  rw [target_end t q _ e]
  have hz : q .sun ≠ Pos.moon := by rw [← e]; apply q.injective.ne; cases v:t.wing <;> simp [target,v]
  have hy : q (remote t) ≠ Pos.moon := by rw [← e]; apply q.injective.ne; cases v:t.wing <;> simp [target,remote,v]
  rw [note0 _ _ hz,note0 _ _ hy]
  change (_,_,_,_,_, (slide (prefixO t q x)).symm ((package k j i).cast.symm b.1),b.2) = _
  rw [lineShift]
variable {l : X→ℕ}
variable (f : (x:X) → Addr P G R S H L i x→Tree)
variable (hv : Manifest _ l f)
include D hP hG hR hS h hv
set_option maxHeartbeats 500000 in
theorem straight (q : Pos≃Pos) (t : Turn) (a : t.shift=1 ∨ t.shift=-1) (e : q (target t)=.moon) :
    let s := Series0 P G R S H L i
    Fleet r l s s f (fun x => Strip.Optic.travel
      (invoke (agent q (walk t)) (P x) (G x) (R x) (S x)) (f x)) := by
  let A x := Queue (H x) (L x) (i x)
  let I x := fore (P x) (G x) (R x) (A x)
  let Q x := Qt H L i x
  let b x := layout (S x)
  let N x := extent H L i x
  let v x := line 2 (N x)
  let T x := ((foreOrder (P x) (G x) (R x) (Q x)).cart ((v x).cart (b x)))
  let k x := (package (H x) (L x) (i x))
  let g x := (joinD (Q x) (P x) (G x) (R x) (S x)).thenDo
    ((Adopt.same (foreOrder (P x) (G x) (R x) (Q x))).split ((k x).split (Adopt.same (b x))))
  apply Fleet.align _ _ (t:=T) (u:=T) g g
  have z := scout P G R H L i hP.station hG.station hR.station h
  have hs := terminal (p:=2) (by decide) N h
  let hat (x:X) (v:I x) := send (badge (eye v).1,badge (eye v).2)
  have B : Manifest (fun x => I x × Block 2 (N x) × Pin (S x)) l (fun x=> f x ∘ (g x).cast.symm) :=
    hv.shift _
  apply Fleet.guide z.valid (hs.product hS.station) B hat z.meter (z.offer.monoSize (fun _ => le_rfl) (fun _ => Nat.zero_le _))
  let Z := Sigma I
  let rt := onboard r hat z.meter
  let n := N ∘ (Sigma.fst:Z→X)
  have p {F : Type} [Codec F] (v:X→F) (u : r.Has v) :
      rt.Has (fun x => v x.1) := onboard_small hat z.meter (send ∘ v) u
  have x : rt.Has (fun x:Z=> (badge (eye x.2).1,badge (eye x.2).2)) := onboard_hat hat z.meter
  let y (q : Pos) (x:Z) := eyeAt q x.2
  have use (q0:Pos) : rt.Has (fun u => badge (y q0 u)) := by
    by_cases e:q0=.sun <;>
      simp only [y,eyeAt,e,ite_true,ite_false]
    exact x.ez Easy.fst
    exact x.ez Easy.snd
  -- offset signal
  let o (u:Z) := start t (y (q .sun) u) (y (q (remote t)) u)
  let w (u:Z) : Omega (H u.1) (L u.1) (i u.1) := offsets (o u)
  obtain ⟨W,pf,pg⟩ := revealed
    (H ∘ (Sigma.fst:Z→X)) (L ∘ (Sigma.fst:Z→X)) (i ∘ (Sigma.fst:Z→X))
    (p _ D) (y (q .sun)) (y (q (remote t))) (use _) (use _) t a
  have issued (u:Z) : Holds (n u) (W u) (w u) := pg u
  have ht := (hS.station.adapt hat z.meter b)
  let f0 (u:Z) (b:Block 2 (n u) × Pin (S u.1)) := f u.1 ((g u.1).cast.symm (u.2,b))
  have move := offset (r:=rt) (p:=2) (by decide) n (p _ h) ht W w issued pf f0
    (Manifest.localize (s:=fun (x:X) a b=>f x ((g x).cast.symm (a,b))) B) Pinpoint.unit
  change Fleet rt (fun u:Z=>l u.1) (fun u=> (v u.1).cart (b u.1)) _
    f0 (fun u b => Strip.Optic.travel (invoke (agent q (walk t)) _ _ _ _) (f u.1)
      ((g u.1).cast.symm (u.2,b)))
  suffices e : (fun (u:Z) (b:Block 2 (n u) × Pin (S u.1)) => Strip.Optic.travel
      (invoke (agent q (walk t)) _ _ _ _) (f u.1) ((g u.1).cast.symm (u.2,b))) =
      fun u b => f0 u ((glide (w u)).symm b.1,b.2) by
    simp only [Pinpoint.one,one_mul] at move
    erw [← e] at move
    exact move
  funext u b0
  exact congrArg (f u.1) (focusO u.2 b0 t q e)

end
end Packed

end IntegerMultiplication
end Computability
end OAI
