import OAI.Computability.NearSquareRoot.ScheduleChunkGuardInit
import OAI.Computability.NearSquareRoot.ScheduleChunkWrapper

/-!
# Standalone initialization of a fenced product candidate

A unary width buffer and a chunk-input record are supplied on separate tapes.
Each tape initially has clear endpoint bits. The same finite rule installs
the endpoints and executes the whole candidate at every permitted split.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkWhole

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
open ChunkControl ChunkLoop ChunkTask

noncomputable section
open Classical

abbrev Symbols (d : Driver) (c : Cmd) := Option (Prog.Sym (ChunkDispatch.area (program d c)))
abbrev Tapes (d : Driver) (c : Cmd) := Option (Prog.Ix (ChunkDispatch.area (program d c)))

def delimiter (d : Driver) (c : Cmd) : Symbols d c := some (.inl Ltr.sep)

def unary (d : Driver) (c : Cmd) (R : ℕ) : List (Symbols d c) :=
  List.replicate R (some (.inl (Ltr.bit true)))

def chunkTapes (d : Driver) (c : Cmd) (s : List Ltr) (j : Tapes d c) : List (Symbols d c) :=
  if j = some (ChunkDispatch.output (program d c)) then (s.map Sum.inl).map some else []

abbrev rule (d : Driver) (c : Cmd) :=
  ChunkGuard.controller (delimiter d c) none (guarded d c)
    (false,some (.inl (ChunkDispatch.start (program d c) .load)))

def initial (d : Driver) (c : Cmd) (R : ℕ) (s : List Ltr) :=
  let cmd := program d c
  ChunkGuard.installing (Q := Bool × Option (SM.PC (Prog.Sym (ChunkDispatch.area cmd))
      (ChunkDispatch.Control cmd) (Prog.Ix (ChunkDispatch.area cmd))))
    (ChunkGuard.beforeInit none (unary d c R ++ [delimiter d c]) (chunkTapes d c s))

private theorem initialized (d : Driver) (c : Cmd) (R : ℕ) (s : List Ltr) :
    ChunkControl.initial d c R s =
      ⟨(false,some (.inl (ChunkDispatch.start (program d c) .load))),
        fun j => Uniform.Fence.markedTape (-(R : ℤ)) R (TM.Tape.loaded none (chunkTapes d c s j))⟩ := by
  change TM.Config.mk _ _ = TM.Config.mk _ _
  congr 1
  funext j
  congr 1
  by_cases e : j = some (ChunkDispatch.output (program d c)) <;>
    simp [ChunkGuard.origin, chunkTapes, e]

/-- A successful run includes one complete installation pass and writes the
exact `2n`-bit product as an encoded Boolean list on the physical output tape. -/
def Finished (d : Driver) (C : ℕ) (c : Cmd) (m : Operands → Word)
    (T : ℕ → ℕ) (p : Input) (encode : Word → List Ltr := fun w => (send w).spell) : Prop :=
  ∃ t ≤ (14*C+303)*((p.count+1)*(p.n+T p.u+1)), ∃ z,
    Trace (TM.advance (rule d c)) (initial d c (radius C p.n) (ChunkPhases.input p)) t z ∧
    TM.advance (rule d c) z = none ∧
    TM.whole none (((encode (answer m p)).map Sum.inl).map some)
      (ChunkGuard.data (z.tape (some none))) ∧
    (answer m p).length = 2*p.n ∧ bitValue (answer m p) = bitValue p.x * bitValue p.y

private theorem fit_time (C : ℕ) (p : Input) (T : ℕ → ℕ) :
    4*radius C p.n+7+(6*C+16)*((p.count+1)*(p.n+T p.u+1)) ≤
      (14*C+303)*((p.count+1)*(p.n+T p.u+1)) := by
  let E := (p.count+1)*(p.n+T p.u+1)
  have hn : p.n+1 ≤ E :=
    (show p.n+1 ≤ p.n+T p.u+1 by omega).trans (Nat.le_mul_of_pos_left _ (by omega))
  have hs := Nat.mul_le_mul_left (8*(C+34)) hn
  have he : 0 < E := by dsimp [E]; positivity
  change 4*radius C p.n+7+(6*C+16)*E ≤ (14*C+303)*E
  rw [radius]
  nlinarith only [hs, hn, he]

theorem finish_of_run {d : Driver} {C : ℕ} {c : Cmd} {m : Operands → Word} {T : ℕ → ℕ}
    {p : Input} {t z} {encode : Word → List Ltr}
    (ht : t ≤ (6*C+16)*((p.count+1)*(p.n+T p.u+1)))
    (run : Trace (TM.advance (guarded d c)) (ChunkControl.initial d c (radius C p.n) (ChunkPhases.input p)) t z)
    (halt : TM.advance (guarded d c) z = none)
    (out : TM.whole none (((encode (answer m p)).map Sum.inl).map some) (ChunkGuard.data (z.tape none)))
    (sz : (answer m p).length = 2*p.n) (val : bitValue (answer m p) = bitValue p.x * bitValue p.y) :
    Finished d C c m T p encode := by
  let R := radius C p.n
  let u := unary d c R
  let sep := delimiter d c
  let width := TM.Tape.loaded (Uniform.FenceInit.plain (none : Symbols d c))
    ((u ++ [sep]).map Uniform.FenceInit.plain)
  have hu : u.length = R := by simp [u, unary]
  have hs : sep ∉ u := by simp [sep, u, delimiter, unary]
  have hb : (none : Symbols d c) ∉ u := by simp [u, unary]
  change Trace _ (ChunkControl.initial d c R _) _ _ at run
  rw [initialized, ← hu] at run
  have hist := ChunkGuard.install_then_run sep none (guarded d c)
    (false,some (.inl (ChunkDispatch.start (program d c) .load))) u []
    (chunkTapes d c (ChunkPhases.input p)) hs hb (by simp [sep, delimiter]) run
  refine ⟨4*R+7+t, (Nat.add_le_add_left ht (4*R+7)).trans (fit_time C p T),
    ChunkGuard.executing width z, ?_, ?_, out, sz, val⟩
  · simpa only [hu, rule, sep, initial, width, u, R] using hist
  · exact ChunkGuard.executing_halts sep none (guarded d c) _ width z halt

theorem of_completed {d : Driver} {C : ℕ} {c : Cmd} {m : Operands → Word} {T : ℕ → ℕ}
    {p : Input} (h : Completed d C c m T p) : Finished d C c m T p := by
  obtain ⟨_, ht, _, run, halt, _, out, sz, val⟩ := h
  exact finish_of_run ht run halt out sz val

/-- A bound uniform over the width of the callee program's code. Only its
number of tapes appears in the space constant. All cutoffs, including failures
while installing and abandoned digit multiplications, obey the same bound. -/
theorem trial_space (d : Driver) (C K : ℕ) : ∃ W : ℕ, ∀ c : Cmd,
    Nat.card (Prog.Ix (Prog.sites [] c)) ≤ K → ∀ n budget (s : List Ltr),
      VisitsAtMost (rule d c) (initial d c (radius C n) s) budget (W*(n+1)) := by
  obtain ⟨D,hD⟩ := output_tape_count_overhead d
  refine ⟨(D+K+1)*(16*(C+34)+31),fun c hc n budget s => ?_⟩
  let R := radius C n
  let u := unary d c R
  let sep := delimiter d c
  have hu : u.length = R := by simp [u, unary]
  have hs : sep ∉ u := by simp [sep, u, delimiter, unary]
  have hb : (none : Symbols d c) ∉ u := by simp [u, unary]
  have space := ChunkGuard.installed_visits sep none
    (SM.complete (ChunkDispatch.output (program d c)) (machine (program d c)))
    (some (.inl (ChunkDispatch.start (program d c) .load))) u [] (chunkTapes d c s)
    hs hb (by simp [sep, delimiter]) budget
  obtain ⟨box, card, cover⟩ := space
  refine ⟨box, card.trans ?_, cover⟩
  have cnt : Fintype.card (Option (Tapes d c)) ≤ D+K+1 := by
    rw [Fintype.card_option, ← Nat.card_eq_fintype_card]
    exact Nat.add_le_add_right ((hD c).trans (Nat.add_le_add_left hc D)) 1
  have span : 8*u.length+15 ≤ (16*(C+34)+31)*(n+1) := by
    rw [hu]
    dsimp only [R, radius]
    nlinarith
  exact (Nat.mul_le_mul cnt span).trans_eq (Nat.mul_assoc ..).symm

/-- One fixed driver works with all isolated digit programs and all their
dyadic splits, including installation time. Each linear-space callee has
a single split that succeeds on all sufficiently wide operands. -/
theorem installed_fixed_split :
    ∃ (d : Driver) (C : ℕ),
      (∀ K : ℕ, ∃ W : ℕ, ∀ c : Cmd, Nat.card (Prog.Ix (Prog.sites [] c)) ≤ K →
        ∀ n budget (s : List Ltr), VisitsAtMost (rule d c)
          (initial d c (radius C n) s) budget (W*(n+1))) ∧
      ∀ (c : Cmd) (m : Operands → Word) (T : ℕ → ℕ) (L : ℕ),
        Isolated c m T (fun u => L*(u+1)) →
        (∀ q : EqualWords, (m q.val).length = 2*q.val.1.length) →
        (∀ q : EqualWords, bitValue (m q.val) = bitValue q.val.1 * bitValue q.val.2) →
        ∃ k : ℕ, ∀ p : Input, p.k = k → 2*2^k ≤ p.n → Finished d C c m T p := by
  obtain ⟨d,C,_,h⟩ := fixed_split
  refine ⟨d,C,trial_space d C,?_⟩
  intro c m T L call len val
  obtain ⟨k,hk⟩ := h c m T L call len val
  exact ⟨k, fun p he hn => of_completed (hk p he hn)⟩

private theorem widen {a b : ℕ} {c : Cmd} {r s : Reg Ltr} (h : ChunkPhases.Runs c a r s)
    (hab : a ≤ b) : ChunkPhases.Runs c b r s := by
  obtain ⟨t, ht, run⟩ := h
  exact ⟨t, ht.trans hab, run⟩

theorem raw_driver :
    ∃ (d : Driver) (C : ℕ), ∀ (m : Operands → Word) (p : Input), (answer m p).length = 2*p.n →
      ChunkPhases.Calls d.load d.test d.prepare d.collect d.emit C m p ((answer m p).map Ltr.bit) := by
  obtain ⟨load,test,prepare,collect,emit,C,ctl⟩ := ChunkPhases.controllers
  refine ⟨⟨load,test,prepare,collect,emit.join Schoolbook.unloadCmd⟩, C+32, ?_⟩
  intro m p hlen
  have small : C*(p.n+1) ≤ (C+32)*(p.n+1) := Nat.mul_le_mul_right _ (by omega)
  refine ⟨widen (ctl m p).load_run small, fun t h => widen ((ctl m p).test_run t h) small,
    fun t h => widen ((ctl m p).prepare_run t h) small,
    fun t h w => widen ((ctl m p).collect_run t h w) small, ?_⟩
  obtain ⟨t, ht, run⟩ := (ctl m p).emit_run
  have tail := Schoolbook.unload_run (answer m p) []
  refine ⟨_, ?_, Prog.Run.join run tail⟩
  rw [hlen, Nat.add_mul]
  omega

/-- The standalone variant writes bare MSF bit letters: the emitter physically
removes the list constructors and preserves leading zeros before output copying. -/
theorem installed_raw_fixed_split :
    ∃ (d : Driver) (C : ℕ),
      (∀ K : ℕ, ∃ W : ℕ, ∀ c : Cmd, Nat.card (Prog.Ix (Prog.sites [] c)) ≤ K →
        ∀ n budget (s : List Ltr), VisitsAtMost (rule d c)
          (initial d c (radius C n) s) budget (W*(n+1))) ∧
      ∀ (c : Cmd) (m : Operands → Word) (T : ℕ → ℕ) (L : ℕ),
        Isolated c m T (fun u => L*(u+1)) →
        (∀ q : EqualWords, (m q.val).length = 2*q.val.1.length) →
        (∀ q : EqualWords, bitValue (m q.val) = bitValue q.val.1 * bitValue q.val.2) →
        ∃ k : ℕ, ∀ p : Input, p.k = k → 2*2^k ≤ p.n → Finished d C c m T p (List.map Ltr.bit) := by
  obtain ⟨d,C,ctl⟩ := raw_driver
  refine ⟨d, C, trial_space d C, ?_⟩
  intro c m T L callee width correct
  obtain ⟨k, hk⟩ := Uniform.exists_dyadic_split L
  refine ⟨k, ?_⟩
  intro p he hn
  have fit : L*(p.u+1) ≤ p.n := by
    simpa only [Input.u,Input.r,he] using (hk p.n hn).2
  have answerOK := answer_spec m correct p
  have digits (t : ℕ) (_ : t < p.count) : (ChunkPhases.digitReply m p t).length = 2*p.u := by
    have wd := p.query_width m t
    let a : EqualWords := ⟨_,wd.1.trans wd.2.symm,wd.1.symm ▸ p.width_pos⟩
    simpa only [a,wd.1,ChunkPhases.digitReply,ChunkPhases.digitQuery] using width a
  obtain ⟨t, ht, z, run, halt, _, out⟩ := guarded_run_letters d c m p C (T p.u)
    (ctl m p answerOK.1) digits (by simp [answerOK.1]; omega)
    (fun i hi => digit_of_isolated d c m T _ callee p C i hi fit)
  exact finish_of_run ht run halt out answerOK.1 answerOK.2

end
end ChunkWhole

end NearSquareRoot
end Computability
end OAI
