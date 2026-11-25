import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalRealize
import OAI.Computability.NearSquareRoot.InterchangeROMWordLedger

/-! # A deterministic bank model carrying the exact native request list -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.Physical

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Loom
  InterchangeROM InterchangeROMSequence

variable {R V U L X : Type} [Field R] [Fintype V] [Fintype U] {m : ℕ}
    {t : Spec R V U m} {half : R} {tag : X → Fin m → Bool}
    {fw bw : (X → R) → X → R} {advance : Bank R L X V → Bank R L X V}
    {wide : Bank R L X V → List Tree} {short : Bank R L X U → List Tree}

private theorem append_eq_of_size {E : Type} {a b c d : List E} (h : a.length=c.length) :
    a++b=c++d ↔ a=c ∧ b=d :=
  ⟨fun e => List.append_inj e h,fun ⟨e,f⟩ => e ▸ f ▸ rfl⟩

/-- Fixed bank arities make the saved inputs recoverable from their concatenation. -/
theorem transition_right_unique {n q : ℕ} (hw : ∀ x, (wide x).length=n)
    (hs : ∀ x, (short x).length=q) (iw : Function.Injective wide) (is : Function.Injective short)
    {a : Leaf} {u v w : List Tree}
    (s : Transition t half tag fw bw advance wide short a u v)
    (s' : Transition t half tag fw bw advance wide short a u w) : v=w := by
  have unique {a : Leaf} {u v u' v' : List Tree}
      (l : Transition t half tag fw bw advance wide short a u v)
      (r : Transition t half tag fw bw advance wide short a u' v') (e : u=u') : v=v' := by
    cases l <;> cases r <;>
      simp only [append_eq_of_size,List.length_append,hw,hs,iw.eq_iff,is.eq_iff] at e <;> grind only
  exact unique s s' rfl

private theorem exists_transition {a : Leaf} {u : List Tree} (h : Inputs wide short a u) :
    ∃ v, Transition t half tag fw bw advance wide short a u v := by
  cases h with
  | duplicate x => exact ⟨_,.duplicate x⟩
  | stage x => exact ⟨_,.stage x⟩
  | extract x y => exact ⟨_,.extract x y⟩
  | forward x y => exact ⟨_,.forward x y⟩
  | correct x y => exact ⟨_,.correct x y⟩
  | backward x y => exact ⟨_,.backward x y⟩
  | restore x y z => exact ⟨_,.restore x y z⟩
  | copyCube x y z => exact ⟨_,.copyCube x y z⟩
  | finish x y z w => exact ⟨_,.finish x y z w⟩

/-- Choose the requests from one open run of a typed transition. The
choices are used only in its proof; native code is already fixed. -/
theorem model_of_steps {Q : Type} (job : Job Q) (prog : Leaf → Cmd) (header : Tree)
    (charge : Leaf → List Tree → Allowance) (ok : Leaf → List Tree → List Q → Prop)
    {n q : ℕ} (hw : ∀ x, (wide x).length=n) (hs : ∀ x, (short x).length=q)
    (iw : Function.Injective wide) (is : Function.Injective short)
    (run : ∀ a u v, Transition t half tag fw bw advance wide short a u v →
      ∃ qs, ok a u qs ∧ InterchangeROMSequence.Step job (prog a) header (Task.forest id u) (packet header v) qs
        (charge a u).time (charge a u).cap (charge a u).depth) :
    ∃ (model : Leaf → List Tree → List Tree) (docket : Leaf → List Tree → List Q),
      LeafSemantics model t half tag fw bw advance wide short ∧
        ∀ a u, Inputs wide short a u → ok a u (docket a u) ∧
          InterchangeROMSequence.Step job (prog a) header (Task.forest id u) (packet header (model a u))
            (docket a u) (charge a u).time (charge a u).cap (charge a u).depth := by
  classical
  let tr := Transition t half tag fw bw advance wide short
  let model (a : Leaf) (u : List Tree) := if h : ∃ v, tr a u v then h.choose else []
  have eqn (a u v) (hv : tr a u v) : model a u = v := by
    have hx : ∃ w, tr a u w := ⟨v,hv⟩
    simpa only [model,dite_eq_left hx] using transition_right_unique hw hs iw is hx.choose_spec hv
  have pick (a u) (h : Inputs wide short a u) : ∃ qs, ok a u qs ∧
      InterchangeROMSequence.Step job (prog a) header (Task.forest id u) (packet header (model a u))
        qs (charge a u).time (charge a u).cap (charge a u).depth := by
    obtain ⟨v,hv⟩ := exists_transition (t:=t) (half:=half) (tag:=tag) (fw:=fw) (bw:=bw) (advance:=advance) h
    rw [eqn _ _ _ hv]
    exact run a u v hv
  let docket (a : Leaf) (u : List Tree) := if h : Inputs wide short a u then (pick a u h).choose else []
  refine ⟨model,docket,⟨fun x => eqn _ _ _ (.duplicate x),fun x => eqn _ _ _ (.stage x),
    fun x y => eqn _ _ _ (.extract x y),fun x y => eqn _ _ _ (.forward x y),
    fun x y => eqn _ _ _ (.correct x y),fun x y => eqn _ _ _ (.backward x y),
    fun x y z => eqn _ _ _ (.restore x y z),fun x y z => eqn _ _ _ (.copyCube x y z),
    fun x y z w => eqn _ _ _ (.finish x y z w)⟩,?_⟩
  intro a u hu
  simpa only [docket,dite_eq_left hu] using (pick a u hu).choose_spec

end InterchangeROMRepair.Physical

end

end NearSquareRoot
end Computability
end OAI
