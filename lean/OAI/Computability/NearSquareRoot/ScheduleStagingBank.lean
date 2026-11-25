import OAI.Computability.NearSquareRoot.CommonAlphabetIOPipelineRoute
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSpace

/-!
# Running an active digit machine beside parked controller tapes

Each local tape can start at its own physical address. A fixed symbol
projection and update run the local rule while preserving persistent mark
tracks at their absolute addresses. Tapes outside the chosen bank retain
both their entire contents and their current head positions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingBank

open IntegerMultiplication TM
open CommonAlphabet.Pipeline

variable {A B Q I J : Type}

structure Track (A B : Type) where
  read : B → A
  write : B → A → B

def symbols (p : Track A B) (m : Rule A Q I) : Rule B Q I := fun q seen =>
  (m q (p.read ∘ seen)).map fun a =>
    (a.1, fun j => (p.write (seen j) (a.2 j).1, (a.2 j).2))

/-- Encoders may retain different permanent marker tuples at different
physical addresses. The source machine sees only its data alphabet. -/
structure Frame (p : Track A B) (I : Type) where
  offset : I → ℤ
  enc : I → ℤ → A → B
  read_enc : ∀ i z a, p.read (enc i z a) = a
  write_enc : ∀ i z a v, p.write (enc i z a) v = enc i z v

variable {p : Track A B}

def tape (f : Frame p I) (i : I) (T : Tape A) : Tape B :=
  ⟨f.offset i + T.pos, fun k => f.enc i (f.offset i + T.pos + k) (T.view k)⟩

def config (f : Frame p I) (x : Config A Q I) : Config B Q I :=
  ⟨x.pc,fun j => tape f j (x.tape j)⟩

private theorem tape_apply (f : Frame p I) (i : I) (t : Tape A) (op : A × Move) :
    (tape f i t).apply (p.write ((tape f i t).view 0) op.1,op.2) = tape f i (t.apply op) := by
  rcases op with ⟨a,m⟩
  change Tape.mk _ _ = Tape.mk _ _
  rw [Tape.mk.injEq]
  refine ⟨by simp only [tape,Tape.apply,add_assoc],funext fun k => ?_⟩
  simp only [tape,Tape.apply,add_zero]
  split_ifs with h
  · rw [f.write_enc]
    congr 1
    omega
  · congr 1
    omega

theorem advance_config (p : Track A B) (f : Frame p I) (m : Rule A Q I) (x : Config A Q I) :
    advance (symbols p m) (config f x) = (advance m x).map (config f) := by
  have read : p.read ∘ (fun j => ((config f x).tape j).view 0) = fun j => (x.tape j).view 0 := by
    funext j
    exact f.read_enc ..
  unfold advance symbols
  rw [read,Option.map_map]
  dsimp only [config]
  cases h : m x.pc (fun i => (x.tape i).view 0) with
  | none => rfl
  | some op =>
    obtain ⟨q,act⟩ := op
    simp only [Option.map_some,Function.comp_apply,config,Option.some.injEq,Config.mk.injEq,
      true_and]
    exact funext fun i => tape_apply f i (x.tape i) (act i)

theorem trace (f : Frame p I) (m : Rule A Q I) {x y : Config A Q I} {n : ℕ}
    (h : Trace (advance m) x n y) :
    Trace (advance (symbols p m)) (config f x) n (config f y) := by
  induction h with
  | nil => exact .nil _
  | cons hh _ ih => exact .cons (by rw [advance_config,hh]; rfl) ih

def rule (route : Route I J) (p : Track A B) (m : Rule A Q I) := route.rule (symbols p m)

def parked (route : Route I J) (f : Frame p I) (shelf : J → Tape B) (x : Config A Q I) :
    Config B Q J := ⟨x.pc,route.put (config f x).tape shelf⟩

private theorem parked_eq (r : Route I J) (f : Frame p I) (s : J → Tape B) (x : Config A Q I) :
    parked r f s x = CommonTapes.config r.index s (config f x) := by
  simp only [parked,CommonTapes.config,Route.put_eq,config]

theorem run (r : Route I J) (p : Track A B) (f : Frame p I) (s : J → Tape B)
    (m : Rule A Q I) {x y : Config A Q I} {n : ℕ} (h : Trace (advance m) x n y) :
    Trace (advance (rule r p m)) (parked r f s x) n (parked r f s y) := by
  simp only [rule,Route.rule_eq,parked_eq]
  exact CommonTapes.trace r.index _ s (trace f m h)

theorem halt (r : Route I J) (p : Track A B) (f : Frame p I) (s : J → Tape B)
    (m : Rule A Q I) {x : Config A Q I} (h : advance m x = none) :
    advance (rule r p m) (parked r f s x) = none := by
  rw [rule,Route.rule_eq,parked_eq,CommonTapes.advance_config,advance_config,h]
  rfl

theorem off (r : Route I J) (f : Frame p I) (s : J → Tape B) (x : Config A Q I)
    (j : J) (hj : ¬ ∃ i, r.index i = j) : (parked r f s x).tape j = s j := by
  rw [parked_eq]
  exact CommonTapes.extend_off r.index _ s j hj

theorem inside (r : Route I J) (f : Frame p I) (s : J → Tape B) (x : Config A Q I)
    (i : I) : (parked r f s x).tape (r.index i) = tape f i (x.tape i) := by
  rw [parked_eq]
  exact CommonTapes.extend_apply ..

/-- On every prefix the active heads move by precisely the displacement of
the corresponding isolated run. The bound uses no code-size factor on any
parked shelf. -/
theorem prefix_bounds (r : Route I J) (p : Track A B) (f : Frame p I) (s : J → Tape B)
    (m : Rule A Q I) {x y : Config A Q I} {n S : ℕ} (h : Trace (advance m) x n y)
    (hs : VisitsAtMost m x n S) {u : ℕ} (hu : u ≤ n) {z : Config B Q J}
    (hz : Trace (advance (rule r p m)) (parked r f s x) u z) :
    (∀ i, f.offset i + (x.tape i).pos - S ≤ (z.tape (r.index i)).pos ∧
      (z.tape (r.index i)).pos ≤ f.offset i + (x.tape i).pos + S) ∧
    ∀ j, (¬ ∃ i, r.index i = j) → z.tape j = s j := by
  obtain ⟨v,hv,_⟩ := trace_split h hu
  have eq := trace_endpoint_unique hz (run r p f s m hv)
  subst z
  refine ⟨fun i => ?_, fun j hj => off r f s v j hj⟩
  have h := Uniform.radius_of_visits hs hu hv i
  rw [inside]
  change _ ≤ f.offset i + (v.tape i).pos ∧ f.offset i + (v.tape i).pos ≤ _
  omega

end StagingBank

end NearSquareRoot
end Computability
end OAI
