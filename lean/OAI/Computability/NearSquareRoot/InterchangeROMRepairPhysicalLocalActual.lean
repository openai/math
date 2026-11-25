import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalLocalBank
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalLocalCost
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalRealize

/-! # Executing an ordinary transition on a ragged physical bank -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.LocalTable.Lift

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  InterchangeROM Space Raw

/-- Largest of the five constants for the fixed local operations. -/
def localFactor (p l w s m half : ℕ) (t : Tape) : ℕ :=
  let c k := costFactor k p l w s m half t
  max (c .duplicate) (max (c .extract) (max (c .restore) (max (c .copyCube) (c .finish))))

theorem costFactor_le_localFactor (k : Kind) (p l w s m half : ℕ) (t : Tape) :
    costFactor k p l w s m half t ≤ localFactor p l w s m half t := by
  dsimp only [localFactor]
  cases k <;> omega

theorem primrec_localFactor {X : Type} [Primcodable X]
    {p l w s m half : X → ℕ} {t : X → Tape} (hp : Primrec p) (hl : Primrec l)
    (hw : Primrec w) (hs : Primrec s) (hm : Primrec m) (hh : Primrec half) (ht : Primrec t) :
    Primrec fun x => localFactor (p x) (l x) (w x) (s x) (m x) (half x) (t x) :=
  let e k := primrec_costFactor k hp hl hw hs hm hh ht
  Primrec.nat_max.comp (e .duplicate) (Primrec.nat_max.comp (e .extract)
    (Primrec.nat_max.comp (e .restore) (Primrec.nat_max.comp (e .copyCube) (e .finish))))

theorem computable_localFactor {X : Type} [Primcodable X]
    {p l w s m half : X → ℕ} {t : X → Tape} (hp : Computable p) (hl : Computable l)
    (hw : Computable w) (hs : Computable s) (hm : Computable m) (hh : Computable half) (ht : Computable t) :
    Computable fun x => localFactor (p x) (l x) (w x) (s x) (m x) (half x) (t x) := by
  let Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × Tape
  let f (q : Q) := localFactor q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2
  have pr : Primrec f := primrec_localFactor (X:=Q)
    (p:=fun v => v.1) (l:=fun v => v.2.1) (w:=fun v => v.2.2.1) (s:=fun v => v.2.2.2.1)
    (m:=fun v => v.2.2.2.2.1) (half:=fun v => v.2.2.2.2.2.1) (t:=fun v => v.2.2.2.2.2.2)
    .fst (Primrec.fst.comp .snd) (Primrec.fst.comp (Primrec.snd.comp .snd))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd))))
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))))
  let arg (x : X) : Q := (p x,l x,w x,s x,m x,half x,t x)
  have args : Computable arg := hp.pair (hl.pair (hw.pair (hs.pair (hm.pair (hh.pair ht)))))
  exact Computable.comp (f:=f) (g:=arg) pr.to_comp args

/-- Every ordinary transition emits the exact bank required by the Hermite
script and pays the same computed factor times the address/payload volume. -/
theorem local_transition {p l w s m half : ℕ} [Fact (p+1).Prime] (t : Tape)
    {A X : Type} {P : A → Type} (rows : Series A) (pay : (a : A) → Series (P a))
    (key : (a : A) → P a → X) (H : Tree) (width : ℕ) (hw : ∀ a, (pay a).count ≤ width)
    (hn : 0 < l*w) {tag : X → Fin m → Bool} {fw bw : (X → ZMod (p+1)) → X → ZMod (p+1)}
    {adv : Bank (ZMod (p+1)) (Fin l) X (Fin w) → Bank (ZMod (p+1)) (Fin l) X (Fin w)}
    (route : Leaf → Cmd) {a : Leaf} {xs ys : List Tree}
    (h : Transition (decode p w s m t) (half : ZMod (p+1)) tag fw bw adv
      (bank rows pay key) (bank rows pay key) a xs ys) (hLocal : ¬ Routed a)
    (env : Env) (r : Deck) (base : ℕ) (hd : DeckCap base r) :
    let cap := localFactor p l w s m half t * InterchangeROMStageVolume.mass H rows.count width
    BoundedFits env (choose (fun k => command k p l w s m half t) route a)
      (pile 0 (packet H xs) r) (pile 0 (packet H ys) r) cap (base+cap) cap := by
  let v := InterchangeROMStageVolume.mass H rows.count width
  have one (k : Kind) (x y : List Tree) (hx : domain rows pay p (inputs k l w s) x)
      (hy : eval rows pay k p l w s m half t x = y) :
      let cap := localFactor p l w s m half t * v
      BoundedFits env (command k p l w s m half t) (pile 0 (packet H x) r)
        (pile 0 (packet H y) r) cap (base+cap) cap := by
    subst y
    have step := bounded (half:=half) (m:=m) rows pay k t hn H width hw x hx env r base hd
    obtain ⟨time,space,depth⟩ := charge_le k p l w s m half t rows pay H width hw x hx
    have increase := Nat.mul_le_mul_right v (costFactor_le_localFactor k p l w s m half t)
    exact step.mono (time.trans increase) (Nat.add_le_add_left (space.trans increase) base) (depth.trans increase)
  cases h with
  | duplicate x => exact one .duplicate _ _ ⟨_,rfl⟩ (duplicate rows pay key t x)
  | stage x => exact (hLocal trivial).elim
  | extract x y =>
    apply one .extract _ _ _ (extract rows pay key t x y)
    simp only [bank,←render_cat]
    exact ⟨_,rfl⟩
  | forward x y => exact (hLocal trivial).elim
  | correct x y => exact (hLocal trivial).elim
  | backward x y => exact (hLocal trivial).elim
  | restore x y z =>
    apply one .restore _ _ _ (restore rows pay key t x y z)
    simp only [bank,←render_cat]
    exact ⟨_,rfl⟩
  | copyCube x y z =>
    apply one .copyCube _ _ _ (copyCube rows pay key t x y z)
    simp only [bank,←render_cat]
    exact ⟨_,rfl⟩
  | finish x y z c =>
    apply one .finish _ _ _ (finish rows pay key t x y z c)
    simp only [bank,←render_cat]
    exact ⟨_,rfl⟩

end InterchangeROMRepair.Physical.LocalTable.Lift

end NearSquareRoot
end Computability
end OAI
