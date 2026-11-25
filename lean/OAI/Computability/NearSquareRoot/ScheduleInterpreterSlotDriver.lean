import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlots
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotCommonBlank
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotBackground
import OAI.Computability.NearSquareRoot.ScheduleMultiplication

/-! # Uniform multiplication from one finite indexed candidate interpreter -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.IndexedSlot
open IntegerMultiplication TM ScheduleMachine Filter
variable {A Q I G : Type}

/-- The interpreter reads the actual multiplication input on one tape and its
unary index on another. Its finite transition table is fixed across all slots. -/
structure Source (A Q I : Type) where
  m : Rule A Q I
  start : Q
  inp : I
  idx : I
  out : I
  blank : A
  sep : A
  bit : Bool → A
  unary : A
  decode : A → Option Bool

def literal (a : A) : PublishedAttempt.Symbol A :=
  Rollback.duplicate (.inl (a,false,false))

def symbol (a : A) : SlotLayout.Letter A := (none,literal a)

namespace Source
variable (s : Source A Q I) [Fintype I] [DecidableEq I]

noncomputable def input (n : ℕ) (x : Input n) :=
  (initialConfig s.start s.inp s.bit s.sep s.blank (xbits x) (ybits x)).tape

def Valid (n : ℕ) (x : Input n) (z : List Bool) : Prop :=
  z.length=2*n ∧ bitValue z=bitValue (xbits x)*bitValue (ybits x)

noncomputable def candidate (n : ℕ) (x : Input n) (i : ℕ) :=
  SlotLayout.raw s.start (s.input n x) s.idx s.blank s.unary i

/-- The finite table physically executes its own generation as part of each run. -/
noncomputable def driver (lo hi : ℕ → I → ℤ)
    (setup : Rule (SlotLayout.Letter A) G (SlotLayout.Axis I)) (first : G) :
    MultiplierDriver (SlotLayout.Letter A) G (IndexedSlot.PC Q I) (SlotLayout.Bank I)
      (Config (Fence.Symbol A) (Bool × Q) I) (Config (Fence.Symbol A) (Bool × Q) I) where
  bit := fun b => symbol (s.bit b)
  sep := symbol s.sep
  blank := symbol s.blank
  mark := (some true,literal s.blank)
  inp := some (.inl s.inp)
  out := none
  setup := setup
  beginSetup := first
  executor := SlotBlank.rule (SlotBlank.perm s.blank (literal s.blank))
    (executor s.m s.start s.idx s.out s.blank s.unary s.decode (fun b => literal (s.bit b)))
  beginTrial := entry
  accept := accepted
  work := fun n x j => SlotBlank.tape (SlotBlank.perm s.blank (literal s.blank) (.inr j))
    (SlotLayout.work s.start (s.input n x) s.idx s.blank s.unary (literal s.blank) (lo n) (hi n) 0 0 j)
  tick := tapeTick (Fence.guard s.m) (fun q => !q.1)
  candidate := fun n x i => Fence.marked (lo n) (hi n) false (s.candidate n x i)

omit [Fintype I] in
theorem input_origins (n : ℕ) (x : Input n) (j : I) : (s.input n x j).pos=0 := by
  simp [input,initialConfig,Tape.loaded]

omit [Fintype I] [DecidableEq I] in
theorem pristine (n : ℕ) (x : Input n) (out : s.out ≠ s.inp) :
    (s.input n x s.out).absolute = fun _ => s.blank := by
  funext p
  simp only [input,initialConfig,out,ite_false,Tape.absolute,Tape.loaded,Int.sub_zero]
  cases p <;> simp

/-- The local data needed from the candidate interpreter. Soundness refers to
its raw literal output, and comparison runs include the time spent generating
their own fixed-index programs. The polynomial candidate is required for all
lengths. Each speed comparison is eventual in the input length. -/
structure Runs (lo hi : ℕ → I → ℤ) (K p : ℕ) : Prop where
  letters : Function.Injective s.bit ∧ (∀ b, s.bit b≠s.sep ∧ s.bit b≠s.blank) ∧ s.sep ≠ s.blank
  separate : s.out≠s.idx ∧ s.out≠s.inp ∧ s.idx≠s.inp
  decoding : s.decode s.blank=none ∧ ∀ b, s.decode (s.bit b)=some b
  sound : ∀ n (x : Input n) i {t y}, Trace (advance s.m) (s.candidate n x i) t y →
    advance s.m y=none → ∃ z, Valid n x z ∧ whole s.blank (z.map s.bit) (y.tape s.out)
  fallback : ∀ n (x : Input n), ∃ t y, FencedRun s.m (lo n) (hi n) (s.candidate n x 0) t y ∧
    advance s.m y=none ∧ t+1≤K*(n+1)^p
  fast : ∀ j : ℕ, ∃ i : ℕ, ∃ H : ℝ, 0≤H ∧ ∀ᶠ n in atTop, ∀ x : Input n,
    ∃ t y, FencedRun s.m (lo n) (hi n) (s.candidate n x i) t y ∧ advance s.m y=none ∧
      ((t+1 : ℕ) : ℝ) ≤ H*n*logScale n^((1:ℝ)/2+1/(j+2:ℝ))

/-- The fixed physical fences used by the installer and executor. -/
structure Comparison (lo hi : ℕ → I → ℤ) (width K p : ℕ) : Prop
    extends s.Runs lo hi K p where
  origin : ∀ n j, lo n j ≤ 0 ∧ 0 ≤ hi n j
  widths : ∀ n, (∑ j, (hi n j+1-lo n j).toNat) ≤ width*(n+1)

variable [Finite A]

theorem implementation (lo hi : ℕ → I → ℤ) {W K p D : ℕ} (c : s.Comparison lo hi W K p)
    (setup : Rule (SlotLayout.Letter A) G (SlotLayout.Axis I)) (first : G)
    (init : ∀ n x, ∃ t y, t≤D*(n+1) ∧
      Trace (advance setup) ((s.driver lo hi setup first).initial n x) t y ∧ advance setup y=none ∧
      y.tape = counters (symbol s.blank) (some true,literal s.blank) 0 0 ((s.driver lo hi setup first).work n x)) :
    (s.driver lo hi setup first).Implements D (SlotCost.coefficient I W 2) 120 K p := by
  let d := s.driver lo hi setup first
  have inj : Function.Injective (@symbol A) := by
    intro u v h
    have z := congrArg (fun a : SlotLayout.Letter A => a.2.val) h
    simpa [symbol,literal,Rollback.duplicate] using z
  refine ⟨⟨inj.comp c.letters.1,fun b => ⟨inj.ne (c.letters.2.1 b).1,inj.ne (c.letters.2.1 b).2⟩,
    inj.ne c.letters.2.2,by simp [driver,symbol]⟩,?_,init,?_,?_,?_⟩
  · intro n x j
    exact SlotLayout.published_origins s.start (s.input n x) s.idx s.blank s.unary (literal s.blank)
      (lo n) (hi n) (s.input_origins n x) 0 0 j
  · intro n x i a
    have h := slots s.m s.start (s.input n x) s.idx s.out c.separate.1 s.blank s.unary s.bit
      (literal s.blank) (fun b => literal (s.bit b)) s.decode c.decoding.1 c.decoding.2
      (lo n) (hi n) (s.input_origins n x) (c.origin n) (s.pristine n x c.separate.2.1)
      (Valid n x) (2*n) i a (fun h k => by
        obtain ⟨z,good,out⟩ := c.sound n x i h k
        exact ⟨z,good.1.le,good,out⟩)
    have coded := SlotBlank.attempts (SlotBlank.perm s.blank (literal s.blank))
      (SlotBlank.perm_cursor_eq s.blank (literal s.blank))
      (P' := fun _ z => d.output n x z.tape) (fun _ z ⟨word,valid,out⟩ =>
        ⟨word,by simpa only [d,driver,symbol,SlotBlank.config,SlotBlank.perm_output_eq,SlotBlank.tape_refl] using out,valid⟩) h
    obtain ⟨t,z,tc,run,halt,out⟩ := coded
    have wid := SlotCost.radius_le (i:=i) (a:=a) I (c.widths n) (H := 2) (show 2*n≤2*(n+1) by omega)
    refine ⟨t,z,tc,⟨run.1,?_⟩,halt,out⟩
    intro k hk y pre j
    obtain ⟨ll,rr⟩ := run.2 k hk y pre j
    dsimp only at ll rr ⊢
    omega
  · intro n x
    obtain ⟨t,y,run,halt,tc⟩ := c.fallback n x
    exact ⟨t+1,_,Fence.trial_complete _ _ _ (by omega) run.1 halt (fun hk pre => run.2 _ hk _ pre),tc⟩
  · intro j
    obtain ⟨i,H,hH,he⟩ := c.fast j
    refine ⟨i,H,hH,?_⟩
    filter_upwards [he] with n h x
    obtain ⟨t,y,run,halt,cost⟩ := h x
    exact ⟨t+1,_,Fence.trial_complete _ _ _ (by omega) run.1 halt (fun hk pre => run.2 _ hk _ pre),cost⟩

end Source
end Uniform.IndexedSlot

end NearSquareRoot
end Computability
end OAI
