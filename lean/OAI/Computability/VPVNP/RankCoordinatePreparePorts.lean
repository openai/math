import OAI.Computability.VPVNP.RankCoordinateArgumentStage
import OAI.Computability.VPVNP.RankCoordinateLabelWord

/-! # Shared advice and live ports of the two slice readers

The two machines read the same root templates, selector bank, and zero label
register. One advised scale is reserved for each operation. Dynamic register
zero and register one directly read the evaluator's two basis indices, and
the label converter directly reads its unary label. All three return intact.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.Prepare

open RAMTape UniversalCountStack BurstRAM NativeReader

/-- Paired-root workspace for the denominator and numerator determinant queries and their
finite-field quotient. The numerator’s entry workspace also carries the replacement-row and
target arguments. -/
abbrev Root (D K : Type) := RootInit.RootHost D (ArgumentStage.Num K)
/-- The combined root banks, dynamic ordinal registers, and unary-label workspace needed for
preparation. -/
abbrev Parts (D K T : Type) := Root D K ⊕ (Dynamic.Host T ⊕ UnaryWord.Port)
/-- Immutable preparation advice, including the root images and the operation-dependent scale
words. -/
abbrev Advice (D K T : Type) := Parts D K T ⊕ Bool
/-- Writable preparation stacks, with an additional temporary port for copying. -/
abbrev Work (D K T : Type) := Parts D K T ⊕ Unit
/-- The reader bus carrying the immutable advice and the writable preparation banks separately. -/
abbrev Ports (D K T : Type) := Bus (Advice D K T) (Work D K T)

variable {D K T : Type}

/-- Assemble the saved determinant roots, dynamic-register image, unary-label image, and the
two scale words as advice. -/
def advice (root : Stacks (Root D K)) (dyn : Stacks (Dynamic.Host T)) (label : Stacks UnaryWord.Port)
    (scale : Bool → List Bool) : Stacks (Advice D K T) := Sum.elim (Sum.elim root (Sum.elim dyn label)) scale

/-- Assemble the live preparation workspace with an initially empty copying stack. -/
def work (root : Stacks (Root D K)) (dyn : Stacks (Dynamic.Host T)) (label : Stacks UnaryWord.Port) : Stacks (Work D K T) :=
  Sum.elim (Sum.elim root (Sum.elim dyn label)) (fun _ => [])

/-- Embed the collection of prepared stacks into the writable bank. -/
def parts : Parts D K T ↪ Work D K T := ⟨Sum.inl,Sum.inl_injective⟩
/-- Embed both determinant-root banks into the preparation workspace. -/
def root : Root D K ↪ Work D K T := ⟨Sum.inl ∘ Sum.inl,Sum.inl_injective.comp Sum.inl_injective⟩
/-- Place the dynamic coordinate registers and ordinal-reader stacks in the preparation
workspace. -/
def dyn : Dynamic.Host T ↪ Work D K T := ⟨Sum.inl ∘ Sum.inr ∘ Sum.inl,Sum.inl_injective.comp (Sum.inr_injective.comp Sum.inl_injective)⟩
/-- Place the unary-to-binary label converter in the preparation workspace. -/
def unary : UnaryWord.Port ↪ Work D K T := ⟨Sum.inl ∘ Sum.inr ∘ Sum.inr,Sum.inl_injective.comp (Sum.inr_injective.comp Sum.inr_injective)⟩
/-- The temporary stack used when copying static roots and arguments. -/
def scratch : Work D K T := .inr ()
/-- Access one writable preparation stack through the scalar reader's auxiliary port. -/
def workPort (a : Work D K T) : Ports D K T := .aux (.inr a)
/-- Read the operation-dependent scale word from the immutable advice bank. -/
def scale (b : Bool) : Ports D K T := .aux (.inl (.inr b))

/-- Copy the saved preparation data from advice into its writable counterpart using the
temporary stack. -/
noncomputable def load [Fintype (Parts D K T)] : FiniteRoutine (Ports D K T) :=
  RootInit.load Sum.inl parts scratch

variable [DecidableEq D] [DecidableEq K] [DecidableEq T]

instance partsDecidable : DecidableEq (Parts D K T) := by
  letI : DecidableEq (Submatrix.Work K) := fun a b => Submatrix.instDecidableEqWork a b
  letI : DecidableEq (ArgumentStage.Num K) := inferInstanceAs (DecidableEq (ISA.Port 2 0 ⊕ Submatrix.Work K))
  letI : DecidableEq (GramEngine.Aux D) := inferInstance
  letI : DecidableEq (GramEngine.Aux (ArgumentStage.Num K)) := inferInstance
  letI : DecidableEq (Root D K) := Cramer.SchurPair.instDecidableEqHost
  letI : DecidableEq (Dynamic.Host T) := inferInstance
  exact inferInstanceAs (DecidableEq (Root D K ⊕ (Dynamic.Host T ⊕ UnaryWord.Port)))

theorem load_bounded [Fintype (Parts D K T)] (label current next : List Bool) (r : Stacks (Root D K))
    (d : Stacks (Dynamic.Host T)) (u : Stacks UnaryWord.Port) (scales : Bool → List Bool)
    (A M : ℕ) (rfit : ∀ i, (r i).length ≤ M) (dfit : ∀ i, (d i).length ≤ M) (ufit : ∀ i, (u i).length ≤ M)
    (start : ∀ i, (state label current next [] (advice r d u scales) (fun _ : Work D K T => []) i).length ≤ A) :
    ∃ t ≤ RootInit.loadClock (Parts D K T) M, load.BoundedRun (A+RootInit.loadClock (Parts D K T) M) t
      (state label current next [] (advice r d u scales) (fun _ : Work D K T => []))
      (state label current next [] (advice r d u scales) (work r d u)) := by
  let tpl := Sum.elim r (Sum.elim d u)
  have fit (i : Parts D K T) : (tpl i).length ≤ M := by
    rcases i with i|i|i <;> first | exact rfit i | exact dfit i | exact ufit i
  obtain ⟨t,ht,run⟩ := RootInit.load_runs Sum.inl parts scratch (fun _ h => by contradiction)
    label current next [] (advice r d u scales) (fun _ : Work D K T => []) tpl (fun _ => rfl)
    (fun _ => rfl) rfl M A fit start
  have eq : installStacks parts (fun _ : Work D K T => []) tpl = work r d u := by
    funext i; rcases i with i | i
    · exact installStacks_at parts.injective _ _ i
    · exact installStacks_outside _ _ (fun _ h => by contradiction)
  rw [eq] at run
  exact ⟨t,ht,run⟩

/-- Wire the dynamic selector's current and next registers to the reader's live ordinals and
mount its other ports in workspace. -/
def dynPort (z : Dynamic.Host T) : Ports D K T :=
  if z = .inl (.reg 0) then .current else if z = .inl (.reg 1) then .next else workPort (dyn z)

omit [DecidableEq D] [DecidableEq K] in
theorem dynPort_injective : Function.Injective (dynPort (D := D) (K := K) (T := T)) := by
  intro a b eq; unfold dynPort at eq
  split_ifs at eq <;> simp_all [workPort,dyn]

/-- Wire the unary converter's source to the public label and its other ports to private
preparation stacks. -/
def unaryPort : UnaryWord.Port → Ports D K T
  | .src => .label
  | z => workPort (unary z)

omit [DecidableEq D] [DecidableEq K] [DecidableEq T] in
theorem unaryPort_injective : Function.Injective (unaryPort (D := D) (K := K) (T := T)) := by
  intro a b eq; cases a <;> cases b <;> simp_all [unaryPort,workPort,unary]

/-- Clear the current and next ordinal registers in the saved register image before they are
supplied by the caller. -/
def dormant {w : ℕ} (rs : Dispatch.Regs 8 w) : Dispatch.Regs 8 w :=
  Function.update (Function.update rs 0 0) 1 0

/-- Mount a selector run while leaving the two dormant template registers at
zero. The two active indices are the evaluator's persistent input words. -/
theorem dynamic_bounded {w B u : ℕ} (selector : FiniteRoutine (OrdinalRead.Port T))
    (before after : Stacks T) (rs rs' : Dispatch.Regs 8 w) (h₀ : rs' 0 = rs 0) (h₁ : rs' 1 = rs 1)
    (r : Stacks (Root D K)) (l : Stacks UnaryWord.Port) (label : List Bool) (a : Stacks (Advice D K T))
    (run : (Dynamic.machine selector).BoundedRun B u (Dynamic.bank before rs) (Dynamic.bank after rs'))
    (room : ∀ i, (state label (wordBits (rs 0)) (wordBits (rs 1)) [] a
      (work r (Dynamic.bank before (dormant rs)) l) i).length ≤ B) :
    ((Dynamic.machine selector).onPorts (dynPort (D := D) (K := K))).BoundedRun B u
      (state label (wordBits (rs 0)) (wordBits (rs 1)) [] a (work r (Dynamic.bank before (dormant rs)) l))
      (state label (wordBits (rs 0)) (wordBits (rs 1)) [] a (work r (Dynamic.bank after (dormant rs')) l)) := by
  apply FiniteRoutine.BoundedRun.framed dynPort_injective run room
  · rintro (i|i)
    · cases i with
      | reg j => by_cases j₀ : j = 0 <;> by_cases j₁ : j = 1 <;>
                  simp_all [dynPort,workPort,work,dyn,state,Reader.bank,Dynamic.bank,ISA.bank,dormant]
      | _ => rfl
    · rfl
  · rintro (i|i)
    · cases i with
      | reg j => by_cases j₀ : j = 0 <;> by_cases j₁ : j = 1 <;>
                  simp_all [dynPort,workPort,work,dyn,state,Reader.bank,Dynamic.bank,ISA.bank,dormant]
      | _ => rfl
    · rfl
  · intro k hk; cases k with
    | aux k =>
      rcases k with k | (k | (k|k)) | k
      · rfl
      · rfl
      · by_cases h₀ : k = .inl (.reg 0)
        · subst k; simp [state,Reader.bank,work,Dynamic.bank,ISA.bank,dormant]
        · by_cases h₁ : k = .inl (.reg 1)
          · subst k; simp [state,Reader.bank,work,Dynamic.bank,ISA.bank,dormant]
          · exact (hk k (by simp [dynPort,h₀,h₁,workPort,dyn])).elim
      · rfl
      · rfl
    | _ => rfl

/-- Frob keeps the zero mark. Label calls convert the live unary label to
its one-based binary mark and return the same label on its public port. -/
def labelCall (frobenius : Bool) : FiniteRoutine (Ports D K T) :=
  if frobenius then .ret else LabelWord.machine.onPorts unaryPort

/-- One step for the immediate return in Frobenius mode, or the unary-to-word conversion clock
for the one-based mark of a label operation. -/
def labelTime (frobenius : Bool) (n w : ℕ) := if frobenius then 1 else LabelWord.clock n w

theorem label_bounded {B n w : ℕ} (b : Bool) (hn : n+1 < 2^w) (r : Stacks (Root D K))
    (d : Stacks (Dynamic.Host T)) (current next : List Bool) (a : Stacks (Advice D K T))
    (room : ∀ k, (state (List.replicate n true) current next [] a
      (work r d (UnaryWord.store [] [] (digits w 0) [] [])) k).length ≤ B)
    (hb : max n w+LabelWord.clock n w ≤ B) :
    (labelCall b).BoundedRun B (labelTime b n w)
      (state (List.replicate n true) current next [] a (work r d (UnaryWord.store [] [] (digits w 0) [] [])))
      (state (List.replicate n true) current next [] a (work r d (UnaryWord.store [] [] (digits w (if b then 0 else n+1)) [] []))) := by
  cases b with
  | true => exact .cons room (.goto rfl) (.nil _ _ room)
  | false =>
    apply FiniteRoutine.BoundedRun.framed unaryPort_injective ((LabelWord.machine_bounded n w hn).enlarge hb) room
    · intro i; cases i <;> rfl
    · intro i; cases i <;> rfl
    · intro k hk; cases k with
      | aux k => rcases k with k|(k|(k|k))|k
                 · rfl
                 · rfl
                 · rfl
                 · cases k <;> first | rfl | exact (hk UnaryWord.Port.number rfl).elim
                 · rfl
      | _ => rfl

end RankQuery.Stack.Coordinate.Prepare

end VPVNP
end Computability
end OAI
