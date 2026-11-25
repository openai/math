import OAI.Computability.IntegerMultiplication.Loom.Cube

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open Net Strip Dims Adic Code Port Optic
variable {I J W L : Type} [Fintype J] [DecidableEq J] [Fintype W]
variable {p : ℕ} [NeZero p] {discount : ℝ} {k : I→ℕ}
variable {r : Regime I} (P : (i:I)→Stair (dim J) p (k i+1))
variable (d : Design J W L p discount) (R : Series W) (c : I→ℕ)

abbrev totalLoom := fun i => c i * dim W ^ (k i+1)
abbrev wideView := fun i:I => Frame W (c i) (k i+1)
abbrev level (i:I) := ringArea P d.order i

noncomputable section
set_option backward.isDefEq.respectTransparency false in
-- reduce defeq issues -- maybe option unknown
omit [NeZero p] in
private theorem tray {n l : I→ℕ} (w : (i:I) → fieldView P i → wideView (W:=W) (k:=k) c i→Bead)
    (x : I→Tree) (hL : Rip r n l x (cloth (level P d) (fun i => skein W R (c i) (k i+1)) w)) :
    Rip r n l x (here P d R c (fun i h a y => w i a (show wideView _ i from (y,h)))) := by
  let v (i:I) (a) (x : fuel c (W:=W) (k:=k) i × W) := w i a (show wideView _ i from x)
  exact extract _ (level P d) (fun i => shaped R c i) v hL

private theorem panel (H : r.Small fun i => (P i).ticket)
    (w : (i:I) → fieldView P i → wideView (W:=W) (k:=k) c i → Bead) :
    let m := totalLoom (k:=k) (W:=W) c
    let T i := skein W R (c i) (k i+1)
    let s := level P d
    let A := cloth s T
    report P d.order R r c m
      (∑ w:W,d.train.cost (fun _ => d.quota) w)
      (together r.header (A w)) (A (fun i => w i ∘ swapper _ _ _)) := by
  dsimp only
  let s := level P d
  let m := totalLoom (k:=k) (W:=W) c
  let T (i:I) := skein W R (c i) (k i+1)
  let A (x : (i:I)→fieldView P i→wideView (W:=W) (k:=k) c i → Bead) := cloth s T x
  let pre (i:I) (f : fieldView P i → wideView (k:=k) (W:=W) c i→Bead) :=
    travel (stages d.order (P i).north (P i).isle (P i).south false p (dim J^k i)) f
  let T0 i := tide (1:Matrix J J (Tower p (dim J^k i))) (P i).north (P i).isle (P i).south
  have u := priority P d.order d.large H
  have g (i:I) : (T i).count ≤ m i := by rw [strands]
  have ge (i:I) : (shaped R c (k:=k) i).count ≤ m i := by
    simp only [shaped,strands,totalLoom,m,pow_succ]
    rw [← Nat.mul_assoc]
    exact Nat.le_mul_of_pos_right _ d.roles
  let v := fun i (h:W) a (y : Frame W (c i) (k i)) => pre i (w i) a (show Frame W (c i) (k i+1) from (y,h))
  have hx := star P d R c m ge H v
  let n i := (s i).count
  have entrance : Drive r n m (A w) (A (fun i => pre i (w i))) :=
    curtain d.order P m d.large H T g w false
  have u0 := Rip.twice (Rip.split entrance.again).1 (tray P d R c _ _ entrance)
  let X (i:I) := here P d R c (fun i w => travel (T0 i) (v i (d.route.symm w))) i
  have Xok : Alive r n m X := clear s (shaped R c) R _ u ge
  let surface : View P c W := fun i w x o => travel (T0 i) (v i w) x o
  have cells (w : W) : Rip r n m X (liveData P d.order R c (fun i => surface i w)) := by
    have e := Fatigue.drill R (fun i w => liveData P d.order R c (fun i => travel (T0 i) (v i (d.route.symm w))) i)
      Xok (d.route w)
    simpa only [Equiv.symm_apply_apply] using e
  have hd : Nonempty W := Fintype.card_pos_iff.mp d.roles
  let t := Classical.choice hd
  let y := fun i => travel (T0 i) (pre i (w i))
  have combine : Rip r n m X (A y) :=
    restore s (shaped R c) R
      (fun i a (b : fuel (k:=k) (W:=W) c i × W) => y i a (show Frame W (c i) (k i+1) from b)) 0 t cells
  have exitTask := combine.twice Xok -- not need
  let U := together r.header (A w)
  have stepped : report P d.order R r c m _ U X := hx.preceded u0
  -- pipe blanket here to output using curtain
  have liftq := curtain d.order P m d.large H T g y true
  have eq : (fun i => travel (stages d.order (P i).north (P i).isle (P i).south true p (dim J^k i)) (y i)) =
      fun i => w i ∘ swapper _ _ _ := funext fun i => corner_value d.order P (w i)
  rw [eq] at liftq
  -- need r.header keep through use
  let ah := Rip.header (r:=r) (l:=m) u.1 Regime.self
  have q := Rip.alivePair ah (cloth_size s T u w g)
  exact ((((stepped.pack r.header).preceded (q.twice (Rip.split q).1))).afterTask
    ((combine.left ah).chain ((Rip.split (Rip.alivePair combine.idle ah)).2.twice
      ((Rip.split (Rip.alivePair combine.idle ah)).1) |>.chain liftq)))

-- outer
structure SubZone {D p : ℕ} {W : Type} (w x : Where D p W) : Prop where
  down : x.1+1=w.1
  equalScale : x.site.supplyLimit=w.site.supplyLimit
  equalRoom : x.plates.count=w.plates.count
  passenger : x.2.cargo=w.2.cargo

def timeNow {D p : ℕ} {W} [Fintype W] (x : Where D p W) :=
  x.2.cargo * dim W ^ x.1

-- arbitrary ghost f: Boll of k+1
variable (v : (i:I) → Boll (dim J) p W (k i+1))
theorem transport
    (H : r.header = fun i => (v i).site.ticket) :
    let w (i:I) : Where (dim J) p W := ⟨k i+1,v i⟩
    Hopto (Where.current R) r (fun i => (w i).plates.count) (fun i => timeNow (w i))
      (fun i x => SubZone (w i) x) (∑ w : W,d.train.cost (fun _ => d.quota) w)
      ((Where.current R).issue ∘ w) ((Where.current R).reply ∘ w) := by
  let w (i:I) : Where (dim J) p W := ⟨k i+1,v i⟩
  let P := fun i => (w i).site
  let m (i:I) := (v i).cargo
  have h : r.Small fun i => (P i).ticket := by rw [show (fun i => (P i).ticket) = r.header from H.symm]; exact Regime.self
  let u (i:I) := depthAdopt p (k i) d.order (P i).north (P i).isle (P i).south
  let y (i:I) (a : fieldView P i) := (w i).2.option ((u i).cast a)
  have g := panel P d R m h y
  let B := totalLoom (k:=k) (W:=W) m
  let A := level P d
  have o (i:I) : (w i).plates.count=(level P d i).count := (u i).cost.symm
  have ih : (Where.current R).issue ∘ w = together r.header
      (cloth A (fun i => skein W R (m i) (k i+1)) y) := by
    rw [H]
    funext i
    apply congrArg (Tree.fork (v i).site.ticket)
    exact (u i).packet _
  have jh : (Where.current R).reply ∘ w =
      (cloth A (fun i => skein W R (m i) (k i+1)) (fun i => y i ∘ swapper _ _ _)) := by
    funext i
    change stripe (stock ..) (fun a => (w i).cap R (swapper _ _ _ a))
      = stripe (level P d i) (fun a => (w i).cap R ((u i).cast (swapper _ _ _ a)))
    rw [(u i).packet]
    apply congrArg (stripe _)
    ext a
    rw [preserved]
    rfl
  obtain ⟨e,g,q,c⟩ := g.safe
  change Hopto _ r (fun i => (w i).plates.count) B (fun i x => SubZone (w i) x) _ ((Where.current R).issue ∘ w) ((Where.current R).reply ∘ w)
  simp_rw [o,ih,jh]
  exact ⟨e,fun i x m => ⟨congrArg Nat.succ (g i x m).1,(g i x m).2.1,
    (g i x m).2.2.2.trans (o i).symm,(g i x m).2.2.1⟩,q,c⟩
end
end Loom

end IntegerMultiplication
end Computability
end OAI
