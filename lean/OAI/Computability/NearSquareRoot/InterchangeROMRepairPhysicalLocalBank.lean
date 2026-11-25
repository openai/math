import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalLocalLift

/-! # Ordinary bank semantics for the local commands

Each output slot has its physical label followed by its component lane. Both
orders are the ones used by the ground matrix and the cubic script.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.LocalTable.Lift

open IntegerMultiplication.Code IntegerMultiplication.Strip Raw
variable {A X : Type} {P : A → Type} (rows : Series A) (pay : (a : A) → Series (P a))
    (key : (a : A) → P a → X) {p l w s m half n : ℕ} (t : Tape)

def coords (x : Bank (ZMod (p+1)) (Fin l) X (Fin n)) : Vector P p (l*n) :=
  fun a j => flat fun b => x b (key a j)

def bank (x : Bank (ZMod (p+1)) (Fin l) X (Fin n)) : List Tree :=
  render rows pay (coords key x)

@[simp] theorem bank_length (x : Bank (ZMod (p+1)) (Fin l) X (Fin n)) :
    (bank rows pay key x).length = l*n := render_length ..

private theorem transfer (k : Kind) (p l w s m half : ℕ) (t : Tape)
    (x : Vector P p (inputs k l w s)) (y : Vector P p (outputs k l w s))
    (h : ∀ a j, act _ _ (matrix k p l w s m half t) (x a j) = y a j) :
    eval rows pay k p l w s m half t (render rows pay x) = render rows pay y := by
  rw [eval_render]
  exact congrArg (render rows pay) (funext (fun a => funext (h a)))

theorem duplicate (x : Bank (ZMod (p+1)) (Fin l) X (Fin w)) :
    eval rows pay .duplicate p l w s m half t (bank rows pay key x) =
      bank rows pay key x ++ bank rows pay key x := by
  simp only [bank, ← render_cat]
  apply transfer
  intro a j
  exact act_duplicate t _

variable [Fact (p+1).Prime]

theorem extract (x y : Bank (ZMod (p+1)) (Fin l) X (Fin w)) :
    eval rows pay .extract p l w s m half t (bank rows pay key x ++ bank rows pay key y) =
      bank rows pay key y ++
        (bank rows pay key (gather (decode p w s m t).extract y) ++
         bank rows pay key (gather (decode p w s m t).extract x)) := by
  simp only [bank, ← render_cat]
  apply transfer
  intro a j
  exact act_extract t _ _

theorem restore (u : Bank (ZMod (p+1)) (Fin l) X (Fin w)) (v z : Bank (ZMod (p+1)) (Fin l) X (Fin s)) :
    eval rows pay .restore p l w s m half t
      (bank rows pay key u ++ (bank rows pay key v ++ bank rows pay key z)) =
      (bank rows pay key u ++ bank rows pay key (gather (decode p w s m t).restore z)) ++
        bank rows pay key (gather (decode p w s m t).restore v) := by
  simp only [bank, ← render_cat]
  apply transfer
  intro a j
  exact act_restore t _ _ _

omit [Fact (p+1).Prime] in
theorem copyCube (u v z : Bank (ZMod (p+1)) (Fin l) X (Fin w)) :
    eval rows pay .copyCube p l w s m half t
      ((bank rows pay key u ++ bank rows pay key v) ++ bank rows pay key z) =
      ((bank rows pay key u ++ bank rows pay key v) ++ bank rows pay key z) ++ bank rows pay key u := by
  simp only [bank, ← render_cat]
  apply transfer
  intro a j
  exact act_copyCube t _ _ _

theorem finish (u v z c : Bank (ZMod (p+1)) (Fin l) X (Fin w)) :
    eval rows pay .finish p l w s m half t
      (((bank rows pay key u ++ bank rows pay key v) ++ bank rows pay key z) ++ bank rows pay key c) =
      bank rows pay key (u - (half : ZMod (p+1)) • (c-u) - z + v) := by
  simp only [bank, ← render_cat]
  apply transfer
  intro a j
  exact act_finish t _ _ _ _

/-- Dispatch to a local arithmetic matrix or to one of the four operations
which move rows or read the address mask. -/
def choose {Y : Type} (localOp : Kind → Y) (routed : Leaf → Y) : Leaf → Y
  | .duplicate => localOp .duplicate
  | .extract => localOp .extract
  | .restore => localOp .restore
  | .copyCube => localOp .copyCube
  | .finish => localOp .finish
  | .stage => routed .stage
  | .forward => routed .forward
  | .backward => routed .backward
  | .correct => routed .correct

theorem semantics (route : Leaf → List Tree → List Tree)
    (tag : X → Fin m → Bool) (fw bw : (X → ZMod (p+1)) → X → ZMod (p+1))
    (adv : Bank (ZMod (p+1)) (Fin l) X (Fin w) → Bank (ZMod (p+1)) (Fin l) X (Fin w))
    (hs : ∀ x, route .stage (bank rows pay key x) = bank rows pay key (adv x))
    (hf : ∀ a b : Bank (ZMod (p+1)) (Fin l) X (Fin s),
      route .forward (bank rows pay key a ++ bank rows pay key b) =
        bank rows pay key (sweep fw a) ++ bank rows pay key (sweep fw b))
    (hc : ∀ a b : Bank (ZMod (p+1)) (Fin l) X (Fin s),
      route .correct (bank rows pay key a ++ bank rows pay key b) =
        bank rows pay key (applyTag (decode p w s m t) tag false a b) ++
          bank rows pay key (applyTag (decode p w s m t) tag true a b))
    (hb : ∀ a b : Bank (ZMod (p+1)) (Fin l) X (Fin s),
      route .backward (bank rows pay key a ++ bank rows pay key b) =
        bank rows pay key (sweep bw a) ++ bank rows pay key (sweep bw b)) :
    LeafSemantics (choose (fun k => eval rows pay k p l w s m half t) route)
      (decode p w s m t) (half : ZMod (p+1)) tag fw bw adv
      (bank rows pay key) (bank rows pay key) :=
  ⟨duplicate rows pay key t, hs, extract rows pay key t, hf, hc, hb,
    restore rows pay key t, copyCube rows pay key t, finish rows pay key t⟩

omit [Fact (p+1).Prime] in
theorem domains (route : Leaf → List Tree → Prop)
    (hs : ∀ x : Bank (ZMod (p+1)) (Fin l) X (Fin w), route .stage (bank rows pay key x))
    (hf : ∀ a b : Bank (ZMod (p+1)) (Fin l) X (Fin s),
      route .forward (bank rows pay key a ++ bank rows pay key b))
    (hc : ∀ a b : Bank (ZMod (p+1)) (Fin l) X (Fin s),
      route .correct (bank rows pay key a ++ bank rows pay key b))
    (hb : ∀ a b : Bank (ZMod (p+1)) (Fin l) X (Fin s),
      route .backward (bank rows pay key a ++ bank rows pay key b)) :
    LeafDomains (choose (fun k => domain rows pay p (inputs k l w s)) route)
      (bank (n:=w) (p:=p) (l:=l) rows pay key) (bank (n:=s) (p:=p) (l:=l) rows pay key) := by
  constructor
  · intro x; exact ⟨_,rfl⟩
  · exact hs
  · intro x y
    simp only [bank,←render_cat]; exact ⟨_,rfl⟩
  · exact hf
  · exact hc
  · exact hb
  · intro u v z
    simp only [bank,←render_cat]; exact ⟨_,rfl⟩
  · intro u v z
    simp only [bank,←render_cat]; exact ⟨_,rfl⟩
  · intro u v z c
    simp only [bank,←render_cat]; exact ⟨_,rfl⟩

/-- Assemble the ordinary leaf executions with the commands supplied for
the four routed operations. The predicate specifies precisely those four. -/
def Routed : Leaf → Prop
  | .stage | .forward | .correct | .backward => True
  | _ => False

section

open IntegerMultiplication Space InterchangeROM

variable {p l w s m half : ℕ} (t : Tape) {A : Type} {P : A → Type}
    (rows : Series A) (pay : (a : A) → Series (P a))

theorem realizes (H : Tree) (env : Env) (width : ℕ) (hw : ∀ a, (pay a).count ≤ width) (hn : 0 < l*w)
    (f : Leaf → List Tree → List Tree) (dom : Leaf → List Tree → Prop)
    (q : Leaf → List Tree → Allowance) (c : Leaf → Cmd)
    (hr : ∀ b, Routed b → ∀ x, dom b x → ∀ d base, DeckCap base d →
      BoundedFits env (c b) (pile 0 (packet H x) d) (pile 0 (packet H (f b x)) d)
        (q b x).time (base+(q b x).cap) (q b x).depth) :
    Realizes (choose (fun k => eval rows pay k p l w s m half t) f)
      (choose (fun k => domain rows pay p (inputs k l w s)) dom)
      (choose (fun k => charge p (outputs k l w s) (inputs k l w s) (matrix k p l w s m half t)
        H rows.count width) q) (choose (fun k => command k p l w s m half t) c) H env := by
  intro b x hx d base hd
  cases b with
  | duplicate => exact bounded rows pay .duplicate t hn H width hw x hx env d base hd
  | stage => exact hr .stage trivial x hx d base hd
  | extract => exact bounded rows pay .extract t hn H width hw x hx env d base hd
  | forward => exact hr .forward trivial x hx d base hd
  | correct => exact hr .correct trivial x hx d base hd
  | backward => exact hr .backward trivial x hx d base hd
  | restore => exact bounded rows pay .restore t hn H width hw x hx env d base hd
  | copyCube => exact bounded rows pay .copyCube t hn H width hw x hx env d base hd
  | finish => exact bounded rows pay .finish t hn H width hw x hx env d base hd

end
end InterchangeROMRepair.Physical.LocalTable.Lift

end NearSquareRoot
end Computability
end OAI
