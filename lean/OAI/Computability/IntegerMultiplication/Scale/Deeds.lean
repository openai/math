import OAI.Computability.IntegerMultiplication.Scale.Hoard
import OAI.Computability.IntegerMultiplication.Brief.News

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Scale
open Param Staff Grid Code Brief IntegerMultiplication.Star Strip Carry Dusk
open scoped BigOperators Real
variable {I:Type} {r:Regime I} (n:I→ℕ)
structure Calendar (r:Regime I) (n:I→ℕ) : Prop where
  shines : ∀ i,Season (n i)
  guide : Guide r n
  localRoom : Realizes r (wall ∘ n)
namespace Calendar
variable (q:Calendar r n)
include q
theorem royalty : Realizes r (lanes ∘ n) := q.guide.spread n
theorem fraction : Realizes r (Scale.F ∘ n) :=
  (.times (Realizes.fix _) (q.guide.fund n))
theorem format : Realizes r (Scale.W ∘ n) :=
  (.times (Realizes.fix _) (q.guide.fund n))
theorem rate : Realizes r (Scale.J ∘ n) :=
  ((Figure.of_spoken (q.royalty n)).repeated (.fix 9)).pay (by
    let a:= (diameter _ (q.royalty n)).pow 9
    exact a)
theorem lamp : Realizes r (Scale.L ∘ n) :=
  ((Figure.of_spoken (q.royalty n)).repeated (.fix 26)).pay ((diameter _ (q.royalty n)).pow _)
theorem drills : Realizes r (Scale.K ∘ n) :=
  ((Figure.of_spoken (q.royalty n)).repeated (.fix 18)).pay ((diameter _ (q.royalty n)).pow _)
variable (m:I→ℕ)
theorem levels (p:Realizes r m) :
    Calendar (signal m p) (n ∘ (Sigma.fst:Across m→I)) :=
  ⟨(fun v=> q.shines v.1),q.guide.abroad n p,landing m p _ q.localRoom⟩
end Calendar
variable {n}
theorem birthday (h:∀ i, Season (n i)) :
    Calendar (city n) n := by
  let v := guide_city n
  refine ⟨h,v,(v.side_long n).pay ?_⟩
  exact Dom.base (wall ∘ n)

structure RoomLine (r : Regime I) (n:I→ℕ) (i:(j:I)→Direction (n j)) : Prop extends Calendar r n where
  aux_ : Realizes r (fun j=> (i j).val)
variable (i:(j:I)→Direction (n j))
namespace RoomLine
variable (Q:RoomLine r n i)
abbrev s (x:I) := moduli (n x) (i x)
abbrev t (x:I) := Param.side (n x) (i x)
abbrev d (x:I) := D (n x) (i x)
include Q
theorem targetSize : Realizes r (t i) := by
  apply (Q.guide.length_ n Q.aux_).pay
  exact (diameter _ Q.localRoom).mono (fun j=> (side_le ..).2)
theorem sourceSize : Realizes r (s i) := by
  apply (Q.guide.size_ n Q.aux_).pay
  exact (diameter _ (targetSize i Q)).mono (fun j=> ((Q.shines j).upper (i j)).1)
theorem dose : Realizes r (d i) := by
  let x:= Figure.of_spoken (Q.sourceSize i)
  have h := (Figure.of_spoken (Q.toCalendar.royalty n)).repeated (.fix 16)
  exact ((x.repeated (.fix 2)).quotients h).pay (((diameter (s i) (Q.sourceSize i)).pow 2).mono
    (fun j=>Nat.div_le_self ..))

theorem levels (m:I→ℕ) (p : Realizes r m) :
    RoomLine (signal m p) (n ∘ (Sigma.fst:Across m→I)) (fun x=> i x.1) :=
  ⟨Q.toCalendar.levels n m p,landing m p _ Q.aux_⟩

open IntegerMultiplication.Fourier
abbrev G (i:I):=Grain (Scale.W (n i))
noncomputable abbrev φ (x): G (n:=n) x→ℂ := meaning (Scale.F (n x)) (Scale.W (n x))
omit Q in
theorem headroom (x:I) : (2:ℝ)^Scale.F (n x)+2 < 2^Scale.W (n x) := by
  apply lt_of_le_of_lt _ (model _)
  have h : (1:ℝ)≤Scale.hi (n x) 1000:=hi1 _ _
  gcongr; linarith [mul_le_mul_of_nonneg_right h (show 0≤(2:ℝ)^Scale.F (n x) by positivity)]

theorem launch (k:(x:I)→ Spot (t i x)) (j:(x:I)→ Spot (s i x))
    (h:Figure r (fun x=>(k x).val)) (v:Figure r (fun x=>(j x).val)):
    ∃ f:(x:I)→G (n:=n) x, Satisfactory (fun x=>Scale.W (n x)) r f ∧ ∀ x,
      ‖meaning (Scale.F (n x)) (Scale.W (n x)) (f x)-win (d i x) (k x) (j x)‖≤ err (n x) := by
  have p (x:I) : d i x ≤ 2^(2*P (n x)) := by
    unfold d D Fourier.paramD
    apply (Nat.div_le_self ..).trans
    have e (i:Direction (n x)):
      moduli (n x) i ≤ 2^P (n x) := ((Q.shines x).upper i).1.trans ((Q.shines x).upper i).2
    rw [mul_comm 2,pow_mul]
    gcongr; exact e _
  let H:=Q.toCalendar
  obtain ⟨f,t,e⟩:= winds k (.of_spoken (Q.sourceSize i)) (.of_spoken (Q.targetSize i)) h j v
    (d i) (Scale.F ∘ n) (Scale.W ∘ n) (Scale.P ∘ n)
    (Q.dose i) (H.fraction _) (H.format _) (H.guide.fund _) p (headroom (n:=n))
  exact ⟨_,t,fun x=> (e x).trans (round_n _)⟩
noncomputable abbrev Sieve (a:I):Spot (s i a)→Spot (s i a)→ℝ := mixTable (t i a) (d i a) (nhood (Scale.J (n a))) (Scale.K (n a))
set_option maxHeartbeats 370000 in
theorem settling (u:Bool)
    (a b:(x:I)→Spot (s i x))
    (p:Figure r (fun i=>(a i).val)) (h:Figure r (fun i=>(b i).val)) :
    ∃ f:(x:I)→G (n:=n) x, Satisfactory (Scale.W ∘ n) r f ∧ ∀ x,
      ‖φ (n:=n) x (f x)-Garden.climate u (Sieve i x (a x) (b x)) (s i x)‖≤ err (n x) := by
  let q:=Q.toCalendar
  have hr (x) : ‖Sieve i x (a x) (b x)‖*2^Scale.F (n x)+2<2^Scale.W (n x) := by
    apply lt_of_le_of_lt ?_ (model _)
    rw [Real.norm_eq_abs]; gcongr
    exact (resonances (Q.shines x) _ _ _).trans ((wash_le _).trans (hi_mono (n x) (by decide :24 ≤1000)))
  have V : ∃ f:(x:I)→G (n:=n) x, Satisfactory (Scale.W ∘ n) r f ∧ ∀ x,
      ‖φ (n:=n) x (f x)-Garden.climate u (Sieve i x (a x) (b x)) (s i x)‖≤ 2*Star.drop_ (Scale.F (n x)) :=
    Garden.sheeting (s:=s i) (t:=t i) (r:=r) (D:=d i) (l:=Scale.J ∘ n)
      (m:=Scale.K ∘ n) (F:=Scale.F ∘ n) (W:=Scale.W ∘ n)
      (i:=a) (j:=b)
      (Q.dose i) (Q.sourceSize i) (Q.targetSize i)
      (q.rate n) (q.drills n) p h
      (fun x v=> (q.shines x).mud (i x) v) (q.fraction _) (q.format _) u hr
  obtain ⟨f,t0,e⟩:= V
  exact ⟨f,t0,fun x=> (e x).trans ((mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ) ≤ 3) (drop_p (Scale.F (n x))).le).trans (round_n (n x)))⟩
end RoomLine
end Scale

end IntegerMultiplication
end Computability
end OAI
