import OAI.Computability.IntegerMultiplication.Loom.Graduate

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open Net Strip Strip.Optic Adic Code Port
variable {I J W L : Type} [DecidableEq J] [Fintype J] [Fintype W]
variable {p : ℕ} [NeZero p] {discount : ℝ}
variable {k : I→ℕ} {r : Regime I} (P : (i:I)→Stair (dim J) p (k i+1))
variable (d : Design J W L p discount) (R : Series W) (hc l : I→ℕ)
variable (m : ∀ i,(shaped (k:=k) R hc i).count≤l i)
variable (H : r.Small fun i => (P i).ticket)
variable (v : (i:I)→fieldView P i→fuel (W:=W) (k:=k) hc i→Bead)
noncomputable section
include m H
omit m in
private theorem fuse {a b c : I→Tree} {u w}
    (z : report P d.order R r hc l u (together r.header a) b)
    (y : report P d.order R r hc l w (together r.header b) c)
    (s : Alive r (fun i => (ringArea P d.order i).count) l a)
    (t : Alive r (fun i => (ringArea P d.order i).count) l b) :
    report P d.order R r hc l (u+w) (together r.header a) c := by
  let N := fun i => (ringArea P d.order i).count
  have D : ∀ i,1≤N i := (priority P d.order d.large H).1
  have hx := Rip.header (l:=l) (r:=r) D Regime.self
  have ah := hx.idle
  have q := Rip.alivePair ah s
  have ty := Rip.split q |>.1
  exact (((z.pack r.header).preceded (q.twice ty)).afterTask
    ((Rip.split (Rip.alivePair t ah)).2.twice (Rip.split (Rip.alivePair t ah)).1)).chain y

omit m in
theorem work (m : ∀ i,(shaped (k:=k) R hc i).count≤l i) (M : List (Lag J p)) (h : ∀ a∈M,a.legal (ranking d.order)) :
    report P d.order R r hc l (M.map Lag.prices).sum
      (together r.header (liveData P d.order R hc v))
      (liveData P d.order R hc (fun i => travel (recreation d.order
        (P i).north (P i).isle (P i).south (dim J^k i) M h) (v i))) := by
  have u := priority P d.order d.large H
  have f (v : (i:I)→fieldView P i→fuel (W:=W) (k:=k) hc i→Bead) := cloth_size _ _ u v m
  induction M generalizing v with
  | nil => exact Hopto.tarry (Drive.self u.1 (f v))
  | cons a M ih =>
    have e := crossingDo P d.order R hc l m v d.large H a (h _ List.mem_cons_self)
    specialize ih (fun i => travel (drive P d.order a (h _ List.mem_cons_self) i) (v i)) (fun x h' => h x (List.mem_cons_of_mem _ h'))
    -- placeholder proof goal
    have g := fuse P d R hc l H e ih (f _) (f _)
    simp only [List.map_cons,List.sum_cons,Nat.cast_add]
    exact g -- recreation.defeq

private theorem contracted (A C : L) (h : d.way A C) :
    report P d.order R r hc l (d.quota A C)
      (together r.header (liveData P d.order R hc v))
      (liveData P d.order R hc (fun i => travel
        (tide (d.face (dim J^k i) C-d.face (dim J^k i) A) (P i).north (P i).isle (P i).south) (v i))) := by
  let o := d.path A C h
  have e := work P d R hc l H v m o.moves o.ok
  have h0 i := outward (d.face (dim J^k i) C-d.face (dim J^k i) A)
      (P:=(P i).north) (G:=(P i).isle) (B:=(P i).south) d.order o.moves o.ok (o.goal (dim J^k i))
  apply (show report P d.order R r hc l _ _ _ from ?_).monotone o.paid
  simpa only [h0] using e

abbrev View (P : (i:I)→Stair (dim J) p (k i+1)) (hc : I→ℕ) (W : Type) :=
  (i:I)→W→fieldView P i→Frame W (hc i) (k i)→Bead
variable (V : View P hc W)

abbrev here := swatch (ringArea P d.order) (shaped R hc) R V
open Circuit
def prepare (A : W→L) (a : Hop W L) (V : View P hc W) : View P hc W :=
  fun i w x o => edges A a.label
    (breath (d.face (dim J^k i)) _ _ _ (ZMod 2)) (fun w x => V i w x o) w x
theorem timbers (A : W→L) (a : Hop W L)
    (t : ∀ w,d.way (A w) (a.label w)) :
    report P d.order R r hc l (∑ w,d.quota (A w) (a.label w))
      (together r.header (here P d R hc V))
      (here P d R hc (fun i => coat a (prepare P d hc A a V i))) := by
  have u := priority P d.order d.large H
  have n0 := u.1
  let N i := (ringArea P d.order i).count
  have hx := Rip.header (r:=r) (l:=l) n0 Regime.self
  have f (v : View P hc W) (w : W) := cloth_size _ _ u (fun i => v i w) m
  have g (v : View P hc W) : Alive r N l (here P d R hc v) := clear _ _ R v u m

  have z : report P d.order R r hc l (∑ w,d.quota (A w) (a.label w))
      (together r.header (here P d R hc V))
      (here P d R hc (prepare P d hc A a V)) := by
    apply Hopto.finite (v:=fun i w => liveData P d.order R hc (fun i => prepare P d hc A a V i w) i)
      R
    · intro w
      have := (d.path _ _ (t w)).paid
      exact le_trans (Int.natCast_nonneg _) this
    · intro w
      have x := (Fatigue.drill (r:=r) (n:=N) (l:=l) R (fun i w => liveData P d.order R hc (fun i => V i w) i)
        (g V) w).right hx
      refine (show report P d.order R r hc l _ _ _ from ?_).preceded x
      have e := contracted P d R hc l m H (fun i => V i w) _ _ (t w)
      have idn : (fun i => prepare P d hc A a V i w) = fun i => travel
          (tide (d.face (dim J^k i) (a.label w)-d.face (dim J^k i) (A w))
            (P i).north (P i).isle (P i).south) (V i w) := by
        funext i b o
        exact congrFun (Design.extGate d A a (fun w b => V i w b o) w) b
      simpa only [← idn] using e -- stackRun eta def
    · exact Rip.alivePair hx (g _)
    · exact f _
    exact n0
  exact z.afterTask (bright _ _ R (prepare P d hc A a V) a (g _))

omit m in
theorem action (m : ∀ i,(shaped (k:=k) R hc i).count≤l i) (i0 : W→L) (as : List (Hop W L))
    (t : (Circuit.mk i0 as).smooth d.way) :
    report P d.order R r hc l (∑ w:W,Circuit.costOf (fun _ => d.quota) i0 as w)
      (together r.header (here P d R hc V))
      (here P d R hc (fun i w x o => Circuit.thread
        (breath (d.face (dim J^k i)) _ _ _ (ZMod 2)) 0 i0 as (fun w x => V i w x o) w x)) := by
  have u := priority P d.order d.large H
  have g (v : View P hc W) := clear _ _ R v u m
  induction as generalizing i0 V with
  | nil =>
    simp only [Circuit.costOf,Pi.zero_apply, Finset.sum_const_zero, thread]
    exact Hopto.tarry (Drive.self u.1 (g V))
  | cons a as ih =>
    simp only [Circuit.smooth,Circuit.trail,List.map_cons,List.isChain_cons_cons] at t
    have z := timbers P d R hc l m H V i0 a (fun w => (t w).1)
    have h' (w) := (t w).2
    -- proof
    specialize ih (fun i => coat a (prepare P d hc i0 a V i)) a.label h'
    have c := fuse P d R hc l H z ih (g _) (g _)
    simp only [Circuit.costOf,Finset.sum_add_distrib]
    exact c

theorem star :
    report P d.order R r hc l (∑ w:W,d.train.cost (fun _ => d.quota) w)
      (together r.header (here P d R hc V))
      (here P d R hc (fun i w => travel (tide (1:Matrix J J (Tower p (dim J^k i)))
        (P i).north (P i).isle (P i).south) (V i (d.route.symm w)))) := by
  have h := action P d R hc l H V m _ _ d.assigned
  have q : (fun (i:I) (w:W) (x:fieldView P i) (o:Frame W (hc i) (k i)) =>
        thread (breath (d.face (dim J^k i)) _ _ _ (ZMod 2)) 0 d.train.init d.train.ops (fun w x => V i w x o) w x)
      = (fun i w => travel (tide (1:Matrix J J (Tower p (dim J^k i)))
        (P i).north (P i).isle (P i).south) (V i (d.route.symm w))) := by
    funext i w x o
    obtain ⟨j,rfl⟩ := d.route.surjective w
    rw [Equiv.symm_apply_apply]
    exact congrFun (Design.shape d (fun w x => V i w x o) j) x
  simpa only [q,Circuit.cost] using h
end
end Loom

end IntegerMultiplication
end Computability
end OAI
