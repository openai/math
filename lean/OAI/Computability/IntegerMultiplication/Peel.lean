import OAI.Computability.IntegerMultiplication.Loom.Fare

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
open Strip
variable {X K : Type} [Codec X]
/-- Fixed compiled stride k and rank i. -/
def pluck (k i : ℕ) (l : List X) : List X :=
  let units := l.map (fun _ => tally k)
  let groups := (Piecework.segment units l).1
  (groups.map (fun g => (cutLists (tally 1,(cutLists (tally i,g)).2)).1)).flatten
theorem easyPluck (k i : ℕ) :
    Easy (pluck (X:=X) k i) := by
  let g (l : List X) := (l.map (fun _ => tally k))
  let e := fun l => (Piecework.segment (g l) l).1
  let q := fun (l : List X) => (cutLists (tally 1,(cutLists (tally i,l)).2)).1
  have h : Easy e := by unfold e g; fun_prop
  have m : Easy q := by
    have h' : Easy (fun (x:List X) => (cutLists (tally i,x)).2) :=
      (easy_cut (Easy.pair (Easy.const _) easy_id)).sndCompose
    exact (easy_cut (Easy.pair (Easy.const _) h')).fstCompose
  change Easy (fun l => ((e l).map q).flatten)
  exact (h.compose m.mapping).compose Easy.flatten

omit [Codec X] in
theorem sealed (l : List Tally) :
    (Piecework.segment (X:=X) l []).1 = List.replicate l.length [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [Piecework.segment,cutLists, ih,List.replicate_succ]

omit [Codec X] in
theorem funded (l : List (List X)) (R : List Tally) :
    (Piecework.segment ((l.map (tally ∘ List.length))++R) l.flatten).1 =
      l ++ List.replicate R.length [] := by
  induction l with
  | nil => simp [sealed]
  | cons a l ih =>
    simp only [List.map_cons,List.cons_append,List.flatten_cons,Piecework.segment]
    simp [Piecework.cut_of_length,Function.comp_def, show
      (l.map (fun x => tally (x.length))) = l.map (tally ∘ List.length) from rfl,ih] -- rewriting comp normal
omit [Codec X] in
private theorem token (l : List X) (i : ℕ) (h : i<l.length) :
    (l.drop i).take 1=[l[i]] := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
    cases i
    · rfl
    rw [List.drop_succ_cons]
    exact ih _ (by simp at h; omega)

open List in
omit [Codec X] in
theorem plucked (l : List (List X)) (k i : ℕ) (h : ∀ d∈l,d.length=k)
    (u : List X) (e : l.map (fun d => (d.drop i).take 1) = u.map fun x => [x]) :
    pluck k i l.flatten=u := by
  cases l with
  | nil =>
    have t : u.length=0 := by have := congrArg List.length e; simpa using this.symm
    have t : u=[] := List.length_eq_zero_iff.mp t
    simp [t,pluck,Piecework.segment]
  | cons a l =>
    have hi : 1≤k := by
      -- e gives? possibly k=0 and e l = [[]] but u map singleton, impossible
      cases u with
      | nil => simp at e
      | cons b u =>
        have q := List.cons.inj e |>.1
        have hz := congrArg List.length q
        have hm := h a List.mem_cons_self
        simp at hz
        omega
    let t := a::l
    change ∀ d∈t,d.length=k at h
    change pluck k i t.flatten=u
    generalize ht : List.length t.flatten - t.length=f
    have len : t.flatten.length=t.length*k := by
      generalize t=b at *
      clear e ht
      induction b with
      | nil => simp
      | cons x l ih =>
        have v := h x List.mem_cons_self
        have w := ih (fun d r => h _ (List.mem_cons_of_mem _ r))
        simp [v,w,Nat.add_mul,Nat.add_comm]
    have ht2 : t.length + f = t.flatten.length := by
      have : t.length≤t.length*k := Nat.le_mul_of_pos_right _ hi
      omega
    have hm : t.flatten.map (fun _ => tally k) =
        t.map (tally ∘ List.length) ++ List.replicate f (tally k) := by
      have j : t.map (tally ∘ List.length)=t.map fun _ => tally k := by
        apply List.map_congr_left; intro a ha; rw [Function.comp_apply,h a ha]
      rw [j,List.map_const',List.map_const',← List.replicate_add,ht2]
    simp only [pluck,hm,funded,cutLists,tally_length,List.map_append]
    change List.map (fun d : List X => _) t = _ at e
    simp [e]
    generalize u=m
    induction m <;> simp_all only [List.map_cons,List.flatten_cons,List.singleton_append,List.map_nil,List.flatten_nil]
variable {W L : Type}
omit [Codec X] in
theorem take_series (s : Series W) (b : Series L) (v : L×W→X) (w : W) :
    pluck s.count (s.index w).val ((b.cart s).tab v) = b.tab (fun i => v (i,w)) := by
  -- pluck chunks
  rw [Series.grouped]
  refine plucked _ _ _ ?_ _ ?_
  · intros d hd
    obtain ⟨i,rfl⟩ := (Series.elements ..).mp hd
    simp
  simp_rw [Series.map_tab]
  apply congrArg (b.tab)
  funext i
  unfold Function.comp
  have h : (s.index w).val < (s.tab (fun r => v (i,r))).length := by
    rw [Series.card]; exact Fin.isLt _
  dsimp only
  rw [token _ _ h,Series.get _ _ (s.index w),Equiv.symm_apply_apply]
end Code

namespace Loom
open Code Strip Dims
variable {I X W : Type} [Codec X] {T A : I→Type} {r : Regime I} {n l : I→ℕ} {p : I→Tree}
variable (d : Series W) (s : (i:I)→Series (A i)) (t : (i:I)→Series (T i))
variable (v : (i:I)→A i→T i × W → X)
-- notation for rectangular symbol words
abbrev strip {T' : Type} (s : Series T') (v : T' → X) := stripe s (fun a => send (v a))
theorem extract (_g : Rip r n l p (stackRun s (fun i a => strip ((t i).cart d) (v i a)))) :
    Rip r n l p (stackRun (fun _ => d) (fun i w => stripe (s i)
      fun a => strip (t i) (fun b => v i a (b,w)))) :=
  Fatigue.dry d _ _g.again fun w => by
    unfold stackRun strip at _g; unfold strip
    simp only [stripe_eq'] at _g ⊢
    have h := Fatigue.act (x:=fun i => (s i).tab fun a => ((t i).cart d).tab (v i a)) _g
      (List.map (pluck d.count (d.index w))) ((easyPluck ..).mapping)
    simpa only [Series.map_tab,Function.comp_def,take_series] using h
end Loom

end IntegerMultiplication
end Computability
end OAI
