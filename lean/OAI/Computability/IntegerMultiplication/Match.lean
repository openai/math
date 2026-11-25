import OAI.Computability.IntegerMultiplication.Peel

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
open Strip
variable {X Y Z K : Type} [Codec X] [Codec Y] [Codec Z]

/-- zipSafe, then clip to first list's length. -/
def zipFair (x : X) (y : Y) (l : List X × List Y) :=
  (cutLists (ruler l.1,zipSafe x y l)).1
theorem easy_zip (x : X) (y : Y) : Easy (zipFair x y) :=
  (easy_cut ((Easy.ruler easy_id.fstCompose).pair ((Easy.zipSafe x y)))).fstCompose

omit [Codec X] [Codec Y] in
private theorem pairs_map (v : K→X) (u : K→Y) (l : List K) :
    (l.map v).zip (l.map u)=l.map (fun i => (v i,u i)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

omit [Codec X] [Codec Y] in
theorem fair (l : K→X) (t : K→Y) (k : List K) (x y) :
    zipFair x y (k.map l,k.map t) = k.map (fun i => (l i,t i)) := by
  have len : (k.map l).length=(k.map t).length := by simp
  have j : ∀ (a : List X) (b : List Y), a.length=b.length →
      ∀ (c : List X) (d : List Y), ((a++c).zip (b++d)).take a.length = a.zip b := by
    intro a
    induction a with
    | nil => intro b h c d; simp
    | cons u a ih =>
      intro b h c d
      cases b with
      | nil => simp at h
      | cons v b => simp [ih b (by simpa using h) c d] -- binder order
  unfold zipFair zipSafe cutLists
  rw [ruler_length]
  dsimp only
  rw [j _ _ len,pairs_map]

def lock (f : X × Y→Z) (x : X) (y : Y) (l : List X × List Y) :=
  List.map f (zipFair x y l)
omit [Codec Z] in
omit [Codec X] [Codec Y] in
theorem paired (f : X × Y→Z) (l : K→X) (t : K→Y) (k : Series K) (x y) :
    lock f x y (k.tab l,k.tab t)=k.tab (fun i => f (l i,t i)) := by
  rw [lock,Series.tab,Series.tab,fair,List.map_map]; rfl -- not k.tab after fair... expand
theorem easy_lock (f : X × Y→Z) (q : Easy f) (x y) : Easy (lock f x y) :=
  (easy_zip x y).compose q.mapping
end Code

namespace Loom
open Code Strip
variable {I A X Y Z : Type} [Codec X] [Codec Y] [Codec Z] {T U : I→Type}
variable (s : (i:I)→Series (T i)) (t : (i:I)→Series (U i))
variable {r : Regime I} {n h : I→ℕ} {p : I→Tree}
abbrev cloth (x : (i:I)→T i→U i→X) :=
  stackRun s (fun i a => stripe (t i) (fun b => send (x i a b)))

variable (x : (i:I)→T i→U i→X) (y : (i:I)→T i→U i→Y)
theorem map_open (v : X→Y) (q : Easy v) (e : Rip r n h p (cloth s t x)) :
    Rip r n h p (cloth s t (fun i a b => v (x i a b))) := by
  unfold cloth stackRun at *
  simp only [stripe_eq'] at *
  simpa only [Series.map_tab,Function.comp_def] using Fatigue.act
    (x:=fun i => (s i).tab (fun a => (t i).tab (x i a))) e _ q.mapping.mapping
theorem duo_open (v : X × Y → Z) (a : Rip r n h p (cloth s t x))
    (b : Rip r n h p (cloth s t y)) (e : Easy v) (c : X) (d : Y) :
    Rip r n h p (cloth s t (fun i w m => v (x i w m,y i w m))) := by
  unfold cloth stackRun at *
  simp only [stripe_eq'] at *
  simpa only [paired,Function.comp_def] using
    Fatigue.act (x:=fun i => ((s i).tab (fun w => (t i).tab (x i w)),(s i).tab (fun w => (t i).tab (y i w))))
      (a.twice b) (lock (lock v c d) [] []) (easy_lock _ (easy_lock _ e ..) ..)

variable {W : Type} (z : Series W) (v : (i:I)→T i→U i × W→X)
-- recombine!
theorem restore (x0 : X) (d : W)
    (e : ∀ w, Rip r n h p (cloth s t (fun i a b => v i a (b,w)))) :
    Rip r n h p (stackRun s (fun i a => strip ((t i).cart z) (v i a))) := by
  let use (l : List W) := (fun i a (b : U i) => l.map (fun y => v i a (b,y)))
  have assemble (l : List W) :
      Rip r n h p (cloth s t (use l)) := by
    induction l with
    | nil => exact map_open s t (fun i a b => v i a (b,d)) (fun _ => []) (Easy.const _) (e _)
    | cons k l ih =>
      exact duo_open s t (fun i a b => v i a (b,k)) (use l)
        (fun q : X × List X => q.1::q.2) (e _) ih (by fun_prop) x0 []
  have g := assemble z.explore
  unfold cloth stackRun at g
  simp only [stripe_eq'] at g
  have fh := Fatigue.act (x:=fun i => (s i).tab (fun a => (t i).tab (use z.explore i a))) g
    (List.map List.flatten) Easy.flatten.mapping
  unfold stackRun strip
  simp only [stripe_eq',Series.grouped]
  simp only [Series.map_tab,Function.comp_def] at fh
  exact fh
end Loom

end IntegerMultiplication
end Computability
end OAI
