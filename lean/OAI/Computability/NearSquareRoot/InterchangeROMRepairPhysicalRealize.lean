import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalBudget

/-! # Assembling independently proved physical leaves

A command on an input packet determines its encoded output even when its user
only supplies shape-specific correctness certificates. This lets the top-level
schedule consume the nine physical certificates directly.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.Physical

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  CommonRegisters Space InterchangeROM

private theorem prog_unique {A : Type} {Γ : Scope A} {c : Prog A} {r : Reg A} {n : ℕ} {v : Reg A}
    (h : Prog.Run Γ c r n v) : ∀ {k w}, Prog.Run Γ c r k w → v = w := by
  induction h with
  | pass | push | pop => intro k w g; cases g; rfl
  | look h ih => intro k w g; cases g with | look g => exact ih g
  | join h₁ h₂ ih₁ ih₂ =>
    intro k w g
    cases g with | join g₁ g₂ => obtain rfl := ih₁ g₁; exact ih₂ g₂
  | tie h ih => intro k w g; cases g with | tie g => exact ih g
  | again he h ih =>
    intro k w g
    cases g with
    | again hg run =>
      obtain rfl := Option.some.inj (he.symm.trans hg)
      exact ih run

private theorem spell_split (x : Tree) : ∀ (y : Tree) (u v : List Ltr),
    x.spell ++ u = y.spell ++ v → x=y ∧ u=v := by
  induction x with
  | atom a =>
    intro y u v h
    cases y with
    | atom b => simpa [Tree.spell] using h
    | fork l r => simp [Tree.spell] at h
  | fork a b ih jh =>
    rintro (c|⟨c,d⟩) u v h
    · simp [Tree.spell] at h
    · simp only [Tree.spell,List.cons_append,List.cons.injEq,true_and,List.append_assoc] at h
      obtain ⟨rfl,hh⟩ := ih c _ _ h
      obtain ⟨rfl,rfl⟩ := jh d _ _ hh
      exact ⟨rfl,rfl⟩

private theorem forest_inj : Function.Injective (Task.forest (id : Tree → Tree)) := by
  intro xs
  induction xs with
  | nil => rintro (_|⟨_,_⟩) h <;> simp_all [Task.forest]
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => simp only [Task.forest_cons,Task.forest_nil,reduceCtorEq] at h
    | cons y ys =>
      simp only [Task.forest_cons,Tree.fork.injEq,id_eq] at h
      exact List.cons.injEq .. |>.mpr ⟨h.1,ih h.2⟩

theorem command_returns_unique {h : Tree} {c : Cmd} {env : Env} {r s : Deck} {n k : ℕ}
    {ys zs : List Tree} (h₁ : Fits env c r (pile 0 (packet h ys) s) n)
    (h₂ : Fits env c r (pile 0 (packet h zs) s) k) : ys = zs := by
  obtain ⟨_,_,g₁⟩ := h₁
  obtain ⟨_,_,g₂⟩ := h₂
  have hz := congrFun (prog_unique g₁ g₂) 0
  rw [letters_here,letters_here] at hz
  exact forest_inj (Tree.fork.inj (spell_split _ _ _ _ hz).1).2

variable {R V U L X : Type} [Field R] [Fintype V] [Fintype U] {m : ℕ}

/-- An input and its precise output named by a single physical leaf. -/
inductive Transition (t : Spec R V U m) (half : R)
    (tag : X → Fin m → Bool) (fw bw : (X → R) → X → R) (advance : Bank R L X V → Bank R L X V)
    (wide : Bank R L X V → List Tree) (short : Bank R L X U → List Tree) : Leaf → List Tree → List Tree → Prop
  | duplicate x : Transition _ _ _ _ _ _ _ _ .duplicate (wide x) (wide x ++ wide x)
  | stage x : Transition _ _ _ _ _ _ _ _ .stage (wide x) (wide (advance x))
  | extract x y : Transition _ _ _ _ _ _ _ _ .extract (wide x ++ wide y)
      (wide y ++ (short (gather t.extract y) ++ short (gather t.extract x)))
  | forward a b : Transition _ _ _ _ _ _ _ _ .forward (short a ++ short b)
      (short (sweep fw a) ++ short (sweep fw b))
  | correct a b : Transition _ _ _ _ _ _ _ _ .correct (short a ++ short b)
      (short (applyTag t tag false a b) ++ short (applyTag t tag true a b))
  | backward a b : Transition _ _ _ _ _ _ _ _ .backward (short a ++ short b)
      (short (sweep bw a) ++ short (sweep bw b))
  | restore u v w : Transition _ _ _ _ _ _ _ _ .restore (wide u ++ (short v ++ short w))
      ((wide u ++ wide (gather t.restore w)) ++ wide (gather t.restore v))
  | copyCube u v w : Transition _ _ _ _ _ _ _ _ .copyCube ((wide u ++ wide v) ++ wide w)
      (((wide u ++ wide v) ++ wide w) ++ wide u)
  | finish u v w c : Transition _ _ _ _ _ _ _ _ .finish (((wide u ++ wide v) ++ wide w) ++ wide c)
      (wide (u - half • (c-u) - w + v))

variable {t : Spec R V U m} {half : R}
    {tag : X → Fin m → Bool} {fw bw : (X → R) → X → R}
    {advance : Bank R L X V → Bank R L X V}
    {wide : Bank R L X V → List Tree} {short : Bank R L X U → List Tree}

abbrev Actual (trans : Leaf → List Tree → List Tree → Prop) (prog : Leaf → Cmd)
    (charge : Leaf → List Tree → Allowance) (h : Tree) (env : Env) :=
  ∀ a u v, trans a u v → ∀ r base, DeckCap base r →
    let k := charge a u
    BoundedFits env (prog a) (pile 0 (packet h u) r) (pile 0 (packet h v) r) k.time (base+k.cap) k.depth

/-- The model is used only to prove behavior of the already specified program.
Its choice is never read by the program generator. -/
theorem model_of_actual {c charge h env}
    (act : Actual (Transition t half tag fw bw advance wide short) c charge h env) :
    ∃ model : Leaf → List Tree → List Tree, LeafSemantics model t half tag fw bw advance wide short ∧
      Realizes model (Inputs wide short) charge c h env := by
  classical
  let q := Transition t half tag fw bw advance wide short
  let model (a : Leaf) (u : List Tree) := if hx : ∃ v, q a u v then hx.choose else []
  have run (a u v) (hv : q a u v) : model a u = v := by
    have exists' := Exists.intro v hv
    rw [show model a u = exists'.choose by simp [model,exists']]
    let bg : Deck := fun _ => []
    have cap : DeckCap 0 bg := fun _ => by simp [letters,bg]
    exact command_returns_unique (act a u _ exists'.choose_spec bg 0 cap).fits (act a u _ hv bg 0 cap).fits
  refine ⟨model,⟨fun x => run _ _ _ (.duplicate x), fun x => run _ _ _ (.stage x),
    fun x y => run _ _ _ (.extract x y),fun x y => run _ _ _ (.forward x y),
    fun x y => run _ _ _ (.correct x y),fun x y => run _ _ _ (.backward x y),
    fun x y z => run _ _ _ (.restore x y z),fun x y z => run _ _ _ (.copyCube x y z),
    fun x y z w => run _ _ _ (.finish x y z w)⟩,?_⟩
  intro a u d
  have hex : ∃ v, q a u v := by
    cases d with
    | duplicate x => exact ⟨_,.duplicate x⟩
    | stage x => exact ⟨_,.stage x⟩
    | extract x y => exact ⟨_,.extract x y⟩
    | forward x y => exact ⟨_,.forward x y⟩
    | correct x y => exact ⟨_,.correct x y⟩
    | backward x y => exact ⟨_,.backward x y⟩
    | restore x y z => exact ⟨_,.restore x y z⟩
    | copyCube x y z => exact ⟨_,.copyCube x y z⟩
    | finish x y z c => exact ⟨_,.finish x y z c⟩
  obtain ⟨v,hv⟩ := hex
  rw [run _ _ _ hv]
  exact act a u v hv

end InterchangeROMRepair.Physical

end

end NearSquareRoot
end Computability
end OAI
