import OAI.Computability.IntegerMultiplication.Scale.Deeds

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Scale
open Param Staff Grid Code Brief IntegerMultiplication.Star Strip Carry Dusk IntegerMultiplication.Fourier
variable {I:Type} {r:Regime I} (n:I→ℕ)

theorem desk (q:Calendar r n) :
    ∃ B:(i:I)→ℕ→Grain (W (n i)),
      r.Has (fun i=>Grid.telex (F (n i)) (span_ (n i)) (B i)) ∧
      ∀ (i:I) (g:Fin (wall (n i))), ‖meaning (F (n i)) (W (n i)) (B i g)-Axon.R (span_ (n i)) (g.val:ℕ)‖ ≤ err (n i) := by
  obtain ⟨B,H,u⟩:=Star.shelving (frac:=F ∘ n) (w:=W ∘ n) (k:=ell ∘ n)
    (q.fraction n) (q.format n) (q.guide.tensorSize _) (fun i=> lt_of_le_of_lt
      (show (2:ℝ)*2^F (n i)+2 ≤ hi (n i) 1000*2^F (n i)+2 by
        have h: 2≤hi (n i) 1000 := (way (n i)).trans (hi_mono _ (by decide))
        gcongr)
      (model _)) q.localRoom
  exact ⟨B,H,fun i g=>(u i g).trans (round_n _)⟩

open RoomLine
variable {n} (a:(i:I)→Direction (n i))
variable (Q:RoomLine r n a)

abbrev ord (n:I→ℕ) (i:I) := Grain (W (n i))
-- generalized gather of assignment with supplied estimates per entry
variable (v m : I→ℕ) (V:Realizes r v) (M:Realizes r m)
abbrev Chart i := Fin (v i)→Fin (m i)→ ord n i
abbrev Dossier (f:(i:I)→Chart (n:=n) v m i) (i:I) :=
  List.ofFn fun j=> List.ofFn fun k=> Dusk.mark (f i j k)


private theorem herb_ {Z:I→Type} {C:Type} [Codec C] (f:(i:I)→Z i→C)
    (P:(i:I)→Fin (v i)→Fin (m i)→Z i→Prop)
    (h :
      let R:= signal v V
      let m₁:=m ∘ (Sigma.fst:Across v →I)
      let M₁:Realizes R m₁:=landing v V m M
      let K:=Across m₁
      let H:=signal m₁ M₁
      ∃ x : (i:K)→ Z i.1.1,H.Has (fun i=> f i.1.1 (x i)) ∧ ∀ i:K,P i.1.1 i.1.2 i.2 (x i)):
    ∃ x:(i:I)→Fin (v i)→Fin (m i)→Z i,
      r.Has (fun i=>List.ofFn (fun j:Fin (v i)=> List.ofFn (fun k:Fin (m i)=> f i (x i j k)))) ∧
        ∀ i j k,P i j k (x i j k) := by
  obtain ⟨g,H,e⟩:=h
  let a : Across v→ℕ:= m ∘ Sigma.fst
  let s:= landing v V m M
  let w i j k:=g ⟨⟨i,j⟩,k⟩
  have U := harvest a s (fun i j=> f i.1 (g ⟨i,j⟩)) H
  refine ⟨w,harvest v V (fun i j=> List.ofFn (fun k:Fin (m i)=> f i (w i j k))) U,fun i j k=>e ⟨⟨i,j⟩,k⟩⟩
theorem chorale (P:(i:I)→ Fin (v i)→Fin (m i)→ ord n i→Prop)
    (y:
      let R:= signal v V
      let m₁:=m ∘ (Sigma.fst:Across v →I)
      let M₁:Realizes R m₁:=landing v V m M
      let K:=Across m₁
      let H:=signal m₁ M₁
      ∃ f:(k:K)→ ord n k.1.1,
        H.Has (fun i:K=> Dusk.mark (f i)) ∧ (∀ i:K,P i.1.1 i.1.2 i.2 (f i))) :
    ∃ B:(i:I)→ Chart (n:=n) v m i,
      r.Has (Dossier v m B) ∧ ∀ i j k,P i j k (B i j k) :=
  herb_ v m V M (Z:=fun i=>ord n i) (fun _=>Dusk.mark) P y

include Q
-- A table.
theorem catalog :
    ∃ B:(i:I)→Chart (n:=n) (RoomLine.t a) (RoomLine.s a) i,
      r.Has (Dossier (RoomLine.t a) (RoomLine.s a) B) ∧
      ∀ i x y,‖meaning (F (n i)) (W (n i)) (B i x y)-win (D (n i) (a i)) x y‖ ≤ err (n i) := by
  let v:=RoomLine.t a
  let m:=RoomLine.s a
  let V:= Q.targetSize a
  let M:= Q.sourceSize a
  let P i (x:Fin (v i)) (y:Fin (m i)) (b:ord n i) :=
    ‖meaning (F (n i)) (W (n i)) b-win (D (n i) (a i)) x y‖ ≤ err (n i)
  apply chorale v m V M P
  let R:=signal v V
  let g (x:Across v):=m x.1
  let G:Realizes R g:=landing v V m M
  let K:=Across g
  let T:= (Q.levels a v V)
  have H:= (T.levels _ g G)
  have e:= floor_ g G
  have f:= landing g G _ (floor_ v V)
  exact launch (I:=K) (fun i=>a i.1.1) H (fun i:K=>i.1.2) (fun i:K=>i.2)
    (Figure.of_spoken f) (Figure.of_spoken e)

theorem library (u:Bool) :
    ∃ B:(i:I)→Chart (n:=n) (RoomLine.s a) (RoomLine.s a) i,
      r.Has (Dossier (RoomLine.s a) (RoomLine.s a) B) ∧
      ∀ i x y,
        ‖meaning (F (n i)) (W (n i)) (B i x y)-
          Garden.climate u (RoomLine.Sieve a i x y) (RoomLine.s a i)‖ ≤ err (n i) := by
  let m:=RoomLine.s a
  let M:= Q.sourceSize a
  let P i (x:Fin (m i)) (y:Fin (m i)) (b:ord n i) :=
    ‖meaning (F (n i)) (W (n i)) b-Garden.climate u (RoomLine.Sieve a i x y) (RoomLine.s a i)‖ ≤ err (n i)
  apply chorale m m M M P
  let R:=signal m M
  let g (x:Across m):=m x.1
  let G:Realizes R g:=landing m M m M
  let K:=Across g
  let T:= (Q.levels a m M)
  have H:= (T.levels _ g G)
  have e:= floor_ g G
  have f:= landing g G _ (floor_ m M)
  exact settling (I:=K) (fun i=>a i.1.1) H u (fun i:K=>i.1.2) (fun i:K=>i.2)
    (Figure.of_spoken f) (Figure.of_spoken e)
end Scale

end IntegerMultiplication
end Computability
end OAI
