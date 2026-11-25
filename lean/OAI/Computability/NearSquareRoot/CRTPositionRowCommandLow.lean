import OAI.Computability.NearSquareRoot.CRTPositionWindowRow
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask
import OAI.Computability.NearSquareRoot.ScheduleRegisterAlignEffectiveTask
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomDeck

/-! # Fixed commands for low packing around a generated middle permutation -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionRows.RowCommandLow
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic IntegerMultiplication.Loom
open IntegerMultiplication.Strip NearSquareRoot.Space CommonRegisters GeneratorSyntax
open PositionProgram Window

noncomputable section

abbrev rowVolume (z : Window.Row) := 2^z.1.mid * (2^z.1.lo * z.1.w)

abbrev rawIn := ReservePack.raw Window.natural (fun z : Window.Row => z.1.mid) (fun z => z.1.lo) Window.src
abbrev input := together Window.rowRegime.header rawIn
abbrev saved := ReservePack.restoreRulers Window.natural (fun z : Window.Row => z.1.mid) (fun z => z.1.lo)
abbrev groupedIn := ReservePack.grouped Window.natural (fun z : Window.Row => z.1.mid) (fun z => z.1.lo) Window.src
abbrev groupedOut := ReservePack.grouped Window.natural (fun z : Window.Row => z.1.mid) (fun z => z.1.lo) Window.dst
abbrev middleInput := together (fun z : Window.Row => send (Reflections.table z.1.perm.symm)) groupedIn
abbrev output := ReservePack.raw Window.natural (fun z : Window.Row => z.1.mid) (fun z => z.1.lo) Window.dst

/-- Logical indexing used by the grouped table program. -/
def wide (z : Window.Row) := (line 2 z.1.lo).cart (Window.natural z)

def data (z : Window.Row) (a : Block 2 z.1.mid) (j : Block 2 z.1.lo × Fin z.1.w) : Bead :=
  Window.src z ((prefixView rfl).cast (a,j.1)) j.2

theorem groupedIn_eq :
    groupedIn = cloth (fun z : Window.Row => line 2 z.1.mid) wide data := rfl

theorem groupedOut_eq : groupedOut = cloth (fun z : Window.Row => line 2 z.1.mid) wide
    (fun z a => data z ((permuteNative z.1.perm.symm).symm a)) := by
  funext z
  apply congrArg (stripe _)
  funext a
  apply congrArg (stripe _)
  funext j
  change send (Window.dst z ((prefixView rfl).cast (a,j.1)) j.2) =
    send (Window.src z ((prefixView rfl).cast ((permuteNative z.1.perm.symm).symm a,j.1)) j.2)
  rw [permuteNative_symm_pullback, Equiv.symm_symm]
  exact congrArg (fun t => send (z.1.record t j.2))
    (ReserveTile.lift_view z.1.fit (flatBitPullback z.1.perm) z.2 a j.1)

/-- Before the low reserve pays for the header, each middle record carries
a polynomial overhead in the full address width. -/
def preClock (d : ℕ) (z : Window.Row) :=
  2^z.1.mid * (2^z.1.lo*z.1.w+(z.1.k+1)^d)

private theorem preBound : ∃ d : ℕ,
    BoundedTask (preClock d) (preClock d) input (together saved middleInput) := by
  have hm := fixedRowGlobal Window.hi Window.hasHi Window.hasMid
  have hb := fixedRowGlobal Window.hi Window.hasHi Window.hasLo
  have inv := ReserveProgram.inverseTable_has (fun x : Window => x.perm) Window.hasPerm
  have hh := fixedRowGlobal Window.hi Window.hasHi inv
  have live := ReservePack.raw_alive (r := Window.rowRegime) Window.natural (fun z : Window.Row => z.1.mid)
    (fun z => z.1.lo) Window.src (fun z => z.1.w) (fun z => z.1.pos) (fun z => by simp [Window.natural])
    1 (fun _ _ _ => le_rfl)
  obtain ⟨d,pre⟩ := ReservePack.prepare Window.natural (fun z : Window.Row => z.1.mid)
    (fun z => z.1.lo) Window.src (fun z => z.1.w) (fun z => z.1.pos) hm hb hh live
  refine ⟨d,boundedOfCarries ?_⟩
  have eq (z : Window.Row) : (preClock d z : ℝ) =
      mass Window.rowRegime (fun z : Window.Row => 2^z.1.mid) (fun z => 2^z.1.lo*z.1.w) d z := by
    change ((_ * (_ + (z.1.k+1)^d) : ℕ) : ℝ) = _ * (_ + (z.1.k+1 : ℝ)^d)
    push_cast
    rfl
  rw [show (fun z : Window.Row => (preClock d z : ℝ)) =
      mass Window.rowRegime (fun z => 2^z.1.mid) (fun z => 2^z.1.lo*z.1.w) d from funext eq]
  exact pre

def degree := preBound.choose

/-- One command is chosen on every row, before any restriction on low width. -/
def preCmd : Cmd := preBound.choose_spec.choose

theorem pre_runs_all : EffectiveBoundedTask.Runs preCmd (preClock degree) (preClock degree)
    input (together saved middleInput) := preBound.choose_spec.choose_spec

private theorem postTask : BoundedTask rowVolume rowVolume (together saved groupedOut) output :=
  ReservePack.restoreBounded Window.natural (fun z : Window.Row => z.1.mid)
    (fun z => z.1.lo) Window.dst (fun z => z.1.w) (fun z => z.1.pos) (fun z => by simp [Window.natural])
    1 (fun _ _ _ => le_rfl)

def postCmd : Cmd := postTask.choose

theorem pre_runs {Y : Type} (sel : Y → Window.Row) (low : ∀ y, payloadBits degree (sel y).1.k ≤ (sel y).1.lo) :
    EffectiveBoundedTask.Runs preCmd (rowVolume ∘ sel) (rowVolume ∘ sel)
      (input ∘ sel) (together saved middleInput ∘ sel) := by
  have cap (y : Y) : ((sel y).1.k+1)^degree ≤ 2^(sel y).1.lo*(sel y).1.w :=
    (payload_capacity degree (sel y).1.k (sel y).1.w (sel y).1.pos).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (low y)))
  have bound (y : Y) : preClock degree (sel y)+1 ≤ 2*(rowVolume (sel y)+1) := by
    unfold preClock rowVolume
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    have := Nat.mul_le_mul_left (2^(sel y).1.mid) (cap y)
    omega
  exact (pre_runs_all.on sel).bound 2 2 bound bound

theorem post_runs {Y : Type} (sel : Y → Window.Row) :
    EffectiveBoundedTask.Runs postCmd (rowVolume ∘ sel) (rowVolume ∘ sel)
      (together saved groupedOut ∘ sel) (output ∘ sel) :=
  (show EffectiveBoundedTask.Runs postCmd rowVolume rowVolume (together saved groupedOut) output
    from postTask.choose_spec).on sel

private theorem timeOfRuns {Y : Type} {c : Cmd} {t s : Y → ℕ} {src dst : Y → Tree}
    (h : EffectiveBoundedTask.Runs c t s src dst) : EffectiveTask.Runs c t src dst := by
  obtain ⟨C,run⟩ := h
  exact ⟨C,fun i => LoomRegisters.fits_of_bounded_decks c (src i) (dst i) (C*(t i+1))
    (fun env r b hb => (run i env r b hb).fits)⟩

/-- Preparation and restoration terminate on every geometric row, for every
initial P192 environment and deck. -/
theorem pre_value (z : Window.Row) :
    ∃ n : ℕ, ∀ env, Fits.value env preCmd 0 (input z) (together saved middleInput z) n := by
  obtain ⟨C,h⟩ := timeOfRuns pre_runs_all
  exact ⟨_,h z⟩

theorem post_value (z : Window.Row) :
    ∃ n : ℕ, ∀ env, Fits.value env postCmd 0 (together saved groupedOut z) (output z) n := by
  obtain ⟨C,h⟩ := timeOfRuns (post_runs id)
  exact ⟨_,h z⟩

private theorem park {Y : Type} {c : Cmd} {t : Y → ℕ} {src dst : Y → Tree}
    (h : EffectiveTask.Runs c t src dst) (ruler : Y → Tree) :
    EffectiveTask.Runs (KernelEffectiveFamily.rightCmd c) (fun y => (ruler y).count + t y)
      (together ruler src) (together ruler dst) :=
  command_contract (KernelEffectiveFamily.rightCmd c) from (show Code.Task t src dst from ⟨c,h⟩).right ruler

/-- Compose the generated middle command with two fixed low-suffix commands. -/
def frameCmd (core : Cmd) := (preCmd.join (KernelEffectiveFamily.rightCmd core)).join postCmd

theorem frame_effective {J : Type} [Primcodable J] {core : J → Cmd} (h : Effective ltr core) :
    Effective ltr (fun j => frameCmd (core j)) :=
  ((effective_const _ _).join (KernelEffectiveFamily.effective_right h)).join (effective_const _ _)

theorem frame_within (R : ℕ) : ∃ R' : ℕ, 0 < R' ∧ ∀ c, Within R c → Within R' (frameCmd c) := by
  open Filter in
    obtain ⟨S,hS,h₃,hp,hq⟩ := ((eventually_gt_atTop R).and ((eventually_ge_atTop (3 : ℕ)).and
      ((RegisterSelect.within_eventually preCmd).and (RegisterSelect.within_eventually postCmd)))).exists
  exact ⟨S,by omega,fun c hc => ⟨⟨hp,KernelEffectiveFamily.within_right h₃
    (RegisterSelect.within_mono hS.le c hc)⟩,hq⟩⟩

theorem saved_count (z : Window.Row) : (saved z).count ≤ 7 * rowVolume z := by
  change size (tally _) + size (tally _) + 1 ≤ _
  simp only [size_tally,tally_length,Series.count_cart,lineSize,Window.natural,Series.count_natural]
  have a : 2^z.1.mid * 2^z.1.lo ≤ rowVolume z := by
    unfold rowVolume; rw [← Nat.mul_assoc]; exact Nat.le_mul_of_pos_right _ z.1.pos
  have b : z.1.w ≤ rowVolume z := (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)).trans
    (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  have pos := z.1.pos
  omega

/-- The very same frame routes all rows when the middle command is correct;
the preparatory clock retains its polynomial header cost. -/
theorem frame_runs_all {Y : Type} (sel : Y → Window.Row) (core : Cmd) (t : Y → ℕ)
    (run : EffectiveTask.Runs core t (middleInput ∘ sel) (groupedOut ∘ sel)) :
    EffectiveTask.Runs (frameCmd core)
      (fun y => preClock degree (sel y) + ((saved (sel y)).count+t y) + rowVolume (sel y))
      (input ∘ sel) (output ∘ sel) :=
  ((timeOfRuns (pre_runs_all.on sel)).comp (park run (saved ∘ sel))).comp (timeOfRuns (post_runs sel))

theorem frame_value (z : Window.Row) (core : Cmd) (t : ℕ)
    (run : ∀ env, Fits.value env core 0 (middleInput z) (groupedOut z) t) :
    ∃ n : ℕ, ∀ env, Fits.value env (frameCmd core) 0 (input z) (output z) n := by
  let sel : Unit → Window.Row := fun _ => z
  have h : EffectiveTask.Runs core (fun _ : Unit => t) (middleInput ∘ sel) (groupedOut ∘ sel) := by
    exact ⟨1,fun _ env r => (run env r).mono (by simp)⟩
  obtain ⟨C,done⟩ := frame_runs_all sel core _ h
  exact ⟨_,done ()⟩

/-- Only the saved length ruler is scanned around the call to the middle program. -/
theorem frame_runs {Y : Type} (sel : Y → Window.Row) (low : ∀ y, payloadBits degree (sel y).1.k ≤ (sel y).1.lo)
    (core : Cmd) (t : Y → ℕ) (run : EffectiveTask.Runs core t (middleInput ∘ sel) (groupedOut ∘ sel)) :
    EffectiveTask.Runs (frameCmd core) (fun y => t y + rowVolume (sel y)) (input ∘ sel) (output ∘ sel) := by
  have pre := timeOfRuns (pre_runs sel low)
  have body := park run (saved ∘ sel)
  have post := timeOfRuns (post_runs sel)
  apply ((pre.comp body).comp post).bound 9
  intro y
  have := saved_count (sel y)
  change rowVolume (sel y) + ((saved (sel y)).count + t y) + rowVolume (sel y) + 1 ≤ _
  omega

end
end Controlled.PositionRows.RowCommandLow

end NearSquareRoot
end Computability
end OAI
