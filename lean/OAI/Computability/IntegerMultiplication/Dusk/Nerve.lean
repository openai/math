import OAI.Computability.IntegerMultiplication.Phase.Layout
import OAI.Computability.IntegerMultiplication.Dusk.Trail

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Dusk
open Code Bits Strip Loom
-- template from arbitrary values, can decode and expand in Easy (linear)
abbrev Film := List Bead
noncomputable section
def tie (x : Pair) : Film := (x.1++x.2).map notify.symm
def tore (w : Pair) (x : Film) : Pair :=
  cutLists (ruler w.1,x.map notify)
theorem tied (x y : Pair) (e : x.1.length=y.1.length) :
    tore x (tie y) = y := by
  simp only [tore,tie,List.map_map]
  have q : (notify ∘ ⇑notify.symm)=id := by funext; simp
  simp [q,cutLists,e,List.map_id_fun]
theorem tie_length (x) : (tie x).length=x.1.length+x.2.length := by simp [tie]
@[fun_prop] theorem tie_easy : Easy tie := by
  have h := Easy.finite (show Bool→Bead from notify.symm)
  exact (show Easy (fun i : Pair => i.1++i.2) from by fun_prop).compose h.mapping
@[fun_prop] theorem tore_easy : Easy (fun i : Pair × Film => tore i.1 i.2) := by
  have h : Easy (fun l : Film => l.map notify) := (Easy.finite notify).mapping
  refine easy_cut ((Easy.ruler (Easy.fst (X:=Pair) (Y:=Film)).fstCompose).pair (Easy.snd.compose h))
def spool (x : List Pair) : Film :=
  (x.map tie).flatten
def storm (x : List Pair × Film) :=
  let s := (x.1.map (fun w => ruler (w.1++w.2)))
  let u := (Piecework.segment s x.2).1
  lock (fun p => tore p.1 p.2) ([],[]) [] (x.1,u)
@[fun_prop] theorem spool_easy : Easy spool :=
  tie_easy.mapping.compose Easy.flatten
@[fun_prop] theorem storm_easy : Easy storm := by
  have h : Easy (fun w : Pair => ruler (w.1++w.2)) := by fun_prop
  apply Easy.compose _ (easy_lock _ tore_easy _ [])
  exact Easy.fst.pair (((Easy.fst.compose h.mapping).pair Easy.snd).compose Piecework.easy |>.fstCompose)

variable {k : ℕ} {I : Type}
theorem pays (s : Series I) (v a : I→Pair)
    (h : ∀ i,(a i).1.length=(v i).1.length)
    (g : ∀ i,(a i).2.length=(v i).2.length) :
    storm (s.tab a,spool (s.tab v))=s.tab v := by
  have p (i) : ruler ((a i).1++(a i).2)=tally (tie (v i)).length := by
    suffices d : ∀ (l : Tally),l=tally l.length by simpa only [List.length_append,ruler_length,tie_length,h,g] using d (ruler ((a i).1++(a i).2))
    intro l; exact List.eq_replicate_length.mpr (by simp)
  have q : ((s.tab a).map (fun w => ruler (w.1++w.2))) =
      ((s.tab v).map tie).map (tally ∘ List.length) := by
    simp [Series.map_tab,Function.comp_def,p]
  unfold storm spool
  dsimp only
  rw [q,Piecework.prescribed,Series.map_tab,paired]
  simp [Function.comp_apply,tied _ _ (h _)]

abbrev coat (s : Series I) (x : I→Grain k) :=
  s.tab (mark ∘ x)
theorem film (x : Grain k) : (tie (mark x)).length=2*(k+1) := by
  rw [tie_length,mark,trip_length,trip_length,Nat.two_mul]
def stock (x : Grain k) := (Series.natural (2*(k+1))).untab (tie (mark x))
  (by simpa only [Series.count_natural] using film x)
theorem stockera (x : Grain k) :
    (Series.natural (2*(k+1))).tab (stock x)=tie (mark x) :=
  (Series.natural _).recover _ _

def spark (x : I→Grain k) (i : I × Fin (2*(k+1))) : Bead := stock (x i.1) i.2
def goods (s : Series I) (k : ℕ) :=
  s.cart (Series.natural (2*(k+1)))
theorem investment (s : Series I) (x : I→Grain k) :
    spool (s.tab (mark ∘ x))=(goods s k).tab (spark x) := by
  simp [spool, goods,Series.grouped,spark,stockera,Series.map_tab,Function.comp_def]
theorem uncover (s : Series I) (a b : I→Grain k) :
    storm (s.tab (mark ∘ a), (goods s k).tab (spark b))=s.tab (mark ∘ b) := by
  rw [← investment]; exact pays s _ _ (by simp [mark]) (by simp [mark])

variable {r : Regime I} {n l : I→ℕ} {q : I→Tree}
variable {T F : I→Type} (s : (i:I)→Series (T i)) (f : (i:I)→Series (F i))
variable (w : I→ℕ) (v a : (i:I)→T i → F i → Grain (w i))
abbrev orchid :=
  cloth s f (fun i j => mark ∘ v i j)
abbrev agency :=
  cloth s (fun i => goods (f i) (w i)) (fun i j => spark (v i j))
theorem eruption (u : Rip r n l q (orchid s f w v)) :
    Rip r n l q (agency s f w v) := by
  unfold orchid cloth stackRun at u
  simp only [stripe_eq'] at u
  have d := Fatigue.act
    (x:=fun i => (s i).tab (fun a => (f i).tab (mark ∘ v i a))) u _ spool_easy.mapping
  unfold agency cloth stackRun
  simp only [stripe_eq']
  have H (i:I) (y:T i) : spool ((f i).tab (fun j => mark (v i y j)))=(goods (f i) (w i)).tab (spark (v i y)) := investment ..
  simpa only [Series.map_tab,Function.comp_apply,Function.comp_def,H] using d -- comp_def before investment?
theorem autumn (p : I→Tree)
    (u : Rip r n l p (orchid s f w v)) (h : Rip r n l p (agency s f w a)) :
    Rip r n l p (orchid s f w a) := by
  unfold orchid agency cloth stackRun at *
  simp only [stripe_eq'] at *
  have d := Fatigue.act
    (x:=fun i => ((s i).tab (fun x => (f i).tab (mark ∘ v i x)),(s i).tab (fun x => (goods (f i) (w i)).tab (spark (a i x)))))
    (u.twice h) (lock storm [] []) (easy_lock _ storm_easy [] [])
  have H (i:I) (y:T i) : storm (((f i).tab (fun j => mark (v i y j))), (goods (f i) (w i)).tab (spark (a i y)))=(f i).tab (fun j => mark (a i y j)) := uncover ..
  simp only [paired, H,Function.comp_def] at d; exact d

theorem volume (i : Grain k) : size (mark i)=4*(k+1)+3 := by
  simp [mark,size_word, size_prod, trip_length]; omega
theorem structure_ (z : ∀ i,(f i).count*(w i+1)≤l i) :
    Manifest T l (fun i a => strip (f i) (mark ∘ v i a)) := by
  refine ⟨10,fun i t => ?_⟩
  have q := stripe_size (f i) (send ∘ (mark ∘ v i t)) (4*(w i+1)+3)
    (fun x => show (send (mark _)).count≤_ from (volume _).le)
  specialize z i
  have y : (f i).count ≤ (f i).count*(w i+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  change (strip (f i) _).count ≤ _
  exact q.trans (by nlinarith)
theorem shelter (t : Station r s) (z : ∀ i,(f i).count*(w i+1)≤l i) :
    Alive r (fun i=>(s i).count) l (orchid s f w v) :=
  (structure_ _ w v z).lives t
end
end Dusk

end IntegerMultiplication
end Computability
end OAI
