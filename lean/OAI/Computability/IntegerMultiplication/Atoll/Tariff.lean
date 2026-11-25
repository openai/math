import OAI.Computability.IntegerMultiplication.Atoll.Cord
import OAI.Computability.IntegerMultiplication.Bureau.Sure

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Atoll
open Strip Cap Halo Earth Loom Adic Packed Scale Bureau Thin Phase Param Hook Net Brief Staff
variable {I:Type}(n:I→ℕ)(h:∀i,Season (n i))
abbrev fu:= rest ∘ n
abbrev ku:= ell ∘ n
abbrev ru:= reach ∘ n
abbrev Nu(i:I):= Mbit (fu n i) (ku n i) (ru n i)
abbrev S0(i:I):=dark_ (fu n i) (ku n i) (ru n i)
abbrev S1(i:I):=light_ (fu n i) (ku n i) (ru n i)
abbrev sk i:= Peace (n i)
abbrev Cu:=chunk ∘ n
abbrev Eu(i:I):=Nu n i/Cu n i
abbrev Du(i:I):=Nu n i%Cu n i
abbrev Pu(i:I):Strip.Dims.Tape:=Adic.field 2 (ku n i)
abbrev Wa:= Scale.W ∘ n
abbrev Ju(i:I):=(Earth.spec (Pu n) (fun _=>[]) (Nu n) i).count
include h
theorem price_s (i):(S0 n i).count=Bureau.dim n i ∧ (S1 n i).count=Bureau.dim n i ∧ Ju n i=Bureau.dim n i:= by
  let t:=n i
  let s:= wall t
  let k:=ell t
  let r:=reach t
  let f:=rest t
  have D:(bot (Echo.criterion t)).count=load t := by rw [Series.total,Cap.card]; exact (h i).volume
  have p:= (Acover f k r).thenDo (topline (h i))
  have w:= (Bcover f k r).thenDo (midline (h i))
  have v:(S0 n i).count * s=load t := by
    change (dark_ f k r).count*s=_
    have e:=p.cost
    rw [rim_] at e -- err unfold
    rw [Series.count_cart,Series.count_natural,D] at e
    exact e
  have q:(S1 n i).count*s=load t:=by
    have e:=w.cost
    rw [census (h i),Series.count_cart,Series.count_natural] at e; exact e
  have y : Bureau.dim n i*s=load t := by
    change (outline (n i)).count*s=_
    rw [tallH (h i)]
    exact metric (h i)
  have pos : 0 < s:=Nat.pow_pos (by decide)
  refine ⟨Nat.eq_of_mul_eq_mul_right pos (v.trans y.symm), Nat.eq_of_mul_eq_mul_right pos (q.trans y.symm),
    ((CvA f k r).cost.symm).trans (Nat.eq_of_mul_eq_mul_right pos (v.trans y.symm))⟩
theorem shaping (i):
    2^(0+ku n i+Nu n i+ku n i+0)=load (n i):=by
  let f:= fu n i; let k:=ku n i; let m:=ru n i
  let q:=(splash f k m).thenDo (Thin.bolt_ ..)
  have d:(bot (Echo.criterion (n i))).count=load (n i):= by rw [Series.total,Cap.card]; exact (h i).volume
  have u:(laid f k m).count=load _ := (topline (h i)).cost.trans (rim_ (h i) ▸ d)
  have v:= q.cost
  rw [Adic.lineSize,u] at v
  exact v.symm

omit h
variable {r:Regime I}(g:Guide r n)
include g
theorem statesT : Realizes r (fu n) ∧ Realizes r (ku n) ∧ Realizes r (ru n):=
  ⟨(g.positions n).minused (.fix 1),g.tensorSize n,g.reducedTensor n⟩
theorem statesN : Realizes r (Nu n) :=
  (g.reducedTensor n).plus ((statesT n g).1.times (g.tensorSize n))
include h
omit g in
theorem boundedN (i:I):
    Nu n i≤Param.facing (n i) ∧ Cu n i ≤ Nu n i := by
  have A := h i
  let t:=n i; have T:Season t:=A
  have g:=T.shortWidth
  have K:=T.scatter
  have R :1≤ rest t := by unfold rest scouts; unfold Scale.H0 at K; omega
  have X:=coverP T
  have z:Nu n i≤ (rest t+1)*(ell t) := by
    change reach t+rest t*(ell t) ≤_
    nlinarith
  refine ⟨?_,?_⟩
  · rw [X] at z; exact z
  change chunk t ≤ reach t+rest t*(ell t)
  have y:=Nat.le_mul_of_pos_left (ell t) R
  exact T.batch.1.trans (y.trans (Nat.le_add_left ..))
theorem cardB : Hook.Slice r (Nu n) (Cu n) (Eu n) (Du n) (Wa n) where
  kn:=g.generator n
  en:=(statesN n g).dividing (g.generator n)
  mn:=(statesN n g).rem (g.generator n)
  shape:=funext (fun i=>by unfold Eu Du Curtain.V; exact (by rw [Nat.mul_comm,Nat.div_add_mod]))
  pos i:=(Nat.le_div_iff_mul_le (chunk_pos (n i))).mpr (by rw [one_mul]; exact (boundedN n h i).2)
  small i:=(Nat.mod_lt _ (chunk_pos _)).le
  lock i := Phase.safe_r (Nat.div_le_div_right (c:=Cu n i) (boundedN n h i).1) (h i).safe.2.2
  range_ i := (Nat.div_le_self _ _).trans (((boundedN n h i).1.trans (face_margin _).2).trans
    (by simp only [Wa, Scale.W, Scale.P, Function.comp_apply]; omega))
  area i:= ((boundedN n h i).1.trans (face_margin _).2).trans
    (by simp only [Wa, Scale.W, Scale.P, Function.comp_apply]; omega)
omit h in
theorem paperB : Hook.ArrayCards r (Pu n) (fun _=>[]) (Wa n):=
  ⟨Told.carrier (by decide) _ (g.tensorSize n),Told.nil,
   fun i a q=> Bureau.edge0 _ _ (by simpa [Pu] using q), (Realizes.fix 8192).times (g.fund n)⟩

omit g
noncomputable section
abbrev fee:= Earth.feeK (Cu n) (Eu n)
variable {p q:I→IntegerMultiplication.Code.Tree}
include h
theorem tariffB (v:Breeze (fee n) (logs n) (Ju n) (fU n) p q):
    IntegerMultiplication.Code.Carries (grant n (hue n)) p q := by
  obtain ⟨R,k,t⟩:= v
  obtain ⟨j,H⟩:= massCap n h k
  have M: Ju n=Bureau.dim n:= funext fun i=> (price_s n h i).2.2
  rw [M] at t
  apply t.times (mint_ n (color_p n)) (j*8)
  intro i
  have v : fee n i ≤ 8*hue n i:= permutationFare (n:=n i)
    ((Nat.div_le_self (Nu n i) (Cu n i)).trans ((boundedN n h i).1.trans (face_margin _).2)) (Nat.le_refl _)
  refine (mul_le_mul (H i) v (by linarith [R i]) (by unfold token; positivity)).trans_eq ?_
  unfold Bureau.grant
  push_cast; ring

end
end Atoll

end IntegerMultiplication
end Computability
end OAI
