import OAI.Computability.NearSquareRoot.ScheduleRegisterSelect
import OAI.Computability.NearSquareRoot.ScheduleRegisterConstructors
import OAI.Computability.IntegerMultiplication.Code.FoldLeft

/-! # Finite transition tables on a single data register

The table and its command are data. An effective finite numbering of the
states therefore gives an effective command, even when the states and
the table size vary with the chosen template.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterLookup
open IntegerMultiplication Code CommonRegisters RegisterWitness

/-- The first matching row, with a fixed default on malformed input. -/
def read (table : List (Tree × Tree)) (x : Tree) : Tree :=
  match table with
  | [] => .atom false
  | (u,v)::t => if u = x then v else read t x

/-- Maximum constructor count on one side of a finite table. -/
def limit (f : Tree × Tree → Tree) : List (Tree × Tree) → ℕ
  | [] => 0
  | uv::t => max (f uv).count (limit f t)

theorem le_limit {v : Tree × Tree} (f : Tree × Tree → Tree) {t : List (Tree × Tree)}
    (hv : v ∈ t) : (f v).count ≤ limit f t := by
  induction t with
  | nil => cases hv
  | cons w t ih =>
    rcases List.mem_cons.mp hv with rfl|hv
    · exact le_max_left ..
    · exact (ih hv).trans (le_max_right ..)

/-- The table is compiled into the inspect branches. Its size only affects control. -/
def command (t : List (Tree × Tree)) : Cmd :=
  parse (limit Prod.fst t) 0 (fun x => Task.prepare 0 (read t x))

theorem within {R : ℕ} (hR : 0 < R) (t : List (Tree × Tree)) : Within R (command t) :=
  RegisterSelect.parse_within _ hR _ fun x => (prepare_within (read t x)).mpr hR

theorem read_map {X : Type*} [Codec X] [FiniteState X] (f : X → Tree) (l : List X)
    (x : X) (hx : x ∈ l) : read (l.map fun u => (send u, f u)) (send x) = f x := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    simp only [List.map_cons,read]
    by_cases ha : a = x
    · simp [ha]
    · have he := FiniteState.identify.ne ha
      rw [ite_eq_right he]
      exact ih ((List.mem_cons.mp hx).resolve_left (Ne.symm ha))

theorem run (t : List (Tree × Tree)) (x : Tree) (y : Tree) (e : read t x = y)
    (hm : (x,y) ∈ t) (env : Env) (r : Deck) :
    Fits env (command t) (pile 0 x r) (pile 0 y r) (5*limit Prod.snd t + 4*limit Prod.fst t) := by
  have eout := le_limit Prod.snd hm
  have ein := le_limit Prod.fst hm
  exact (fits_parse _ _ _ _ _ _ _ _ (by rw [e]; exact Task.fits_prepare 0 y env r) ein).mono
    (Nat.add_le_add (Nat.mul_le_mul_left 5 eout) (Nat.mul_le_mul_left 4 ein))

/-- Arbitrary finite transition logic runs at unit cost with a table-dependent constant. -/
theorem finiteTask {X : Type*} [Codec X] [FiniteState X] {R : ℕ} (hR : 0 < R)
    (f : X → Tree) : Timed R (fun _ => 0) send f := by
  classical
  let := Fintype.ofFinite X
  let l := (Finset.univ : Finset X).toList
  have all (x : X) : x ∈ l := by simp [l]
  let t := l.map (fun u => (send u, f u))
  refine ⟨command t,within hR t,5*limit Prod.snd t+4*limit Prod.fst t,fun x env r => ?_⟩
  simpa only [Nat.zero_add,Nat.mul_one] using run t (send x) (f x) (read_map f l x (all x))
    (List.mem_map.mpr ⟨x,all x,rfl⟩) env r

@[simp] theorem sweepBody_within {R : ℕ} (hR : 3 ≤ R) (c : Cmd) :
    Within R (Task.sweepBody c) ↔ Within R c := by
  simp [Task.sweepBody,Within,move,forward,forwardBody,flood,give,pack]
  grind

/-- Read a list of finite letters into a finite state. Three working data registers
suffice for the scan independently of the alphabet and number of states. -/
theorem fold {A S : Type*} [Codec A] [FiniteState A] [Codec S] [FiniteState S]
    {R : ℕ} (hR : 3 ≤ R) (next : S → A → S) :
    Timed R (fun xs : List A × S => size xs.1)
      send (fun xs : List A × S => send (xs.1.foldl next xs.2)) := by
  let U := {p : A × S × Unit // True}
  let V := {p : List A × S × Unit // ∀ x ∈ p.1, True}
  have step := (finiteTask (X := A × S) (R := R) (by omega)
    (fun p => send (next p.2 p.1))).on (fun u : U => (u.val.1,u.val.2.1))
  have scan := register_witness R from Task.foldLeft (Y := Unit) (fun _ => send (X := A))
    (fun _ => send (X := S)) (fun _ => next) (fun _ _ => 0) (D := fun _ _ => True) (forget step)
  let inds (p : List A × S) : V := ⟨(p.1,p.2,()),by simp⟩
  have clock_zero (l : List A) : costSum (fun _ : A => 0) l = 0 := by
    induction l <;> simp_all
  exact (Timed.on scan inds).conform (fun p => by simp [inds,clock_zero,Task.forest_send,size])
    (fun p => by simp [inds,Task.forest_send]) (fun _ => rfl)

end RegisterLookup

end NearSquareRoot
end Computability
end OAI
