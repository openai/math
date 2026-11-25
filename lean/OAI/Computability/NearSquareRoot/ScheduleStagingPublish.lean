import OAI.Computability.NearSquareRoot.ScheduleInterpreterCopy
import OAI.Computability.NearSquareRoot.ShortWordSpace

/-!
# Publishing the final staged word

The controller returns with the read head at the first raw product bit. A
fresh tape has remained blank at zero during the controller run. After one
stationary handoff, simultaneous right moves copy the bits contiguously,
translating the source representation into literal, unmarked output symbols.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingPublish

open IntegerMultiplication TM

variable {A Q I : Type} [DecidableEq I]

def deck (old : I → Tape A) (fresh : Tape A) : Option I → Tape A
  | some i => old i
  | none => fresh

def active (blank : A) (x : Config A Q I) : Config A (Option Q) (Option I) :=
  ⟨some x.pc, deck x.tape (Tape.loaded blank [])⟩

def rule (m : Rule A Q I) (src : I) (decode : A → Option Bool) (bit : Bool → A) :
    Rule A (Option Q) (Option I)
  | some q, h => match m q (fun i => h (some i)) with
    | none => some (none, fun i => (h i,.stay))
    | some (q',op) => some (some q', fun
      | some j => op j
      | none => (h none,.stay))
  | none, h => (decode (h (some src))).map fun b => (none, fun
    | none => (bit b,.right)
    | some j => (h (some j), if j=src then .right else .stay))

variable (m : Rule A Q I) (src : I) (decode : A → Option Bool) (bit : Bool → A) (blank : A)
local notation "pub" => rule m src decode bit

theorem lift_step {x y : Config A Q I} (h : advance m x = some y) :
    advance pub (active blank x) = some (active blank y) := by
  cases op : m x.pc (fun i => (x.tape i).view 0) with
  | none => simp [advance,op] at h
  | some ops =>
    obtain ⟨q,ops⟩ := ops
    simp only [advance,op,Option.map_some,Option.some.injEq] at h
    subst y
    simp only [advance,active,deck,rule,op,Option.map_some,Option.some.injEq,Config.mk.injEq,true_and]
    funext i
    cases i with
    | some j => rfl
    | none => exact SM.Action.apply_stay _

theorem lift_run {x y : Config A Q I} {n : ℕ} (h : Trace (advance m) x n y) :
    Trace (advance pub) (active blank x) n (active blank y) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (lift_step m src decode bit blank h) ih

private theorem handoff (x : Config A Q I) (halt : advance m x = none) :
    advance pub (active blank x) = some ⟨none, (active blank x).tape⟩ := by
  have stop : m x.pc (fun i => (x.tape i).view 0) = none := by
    cases op : m x.pc (fun i => (x.tape i).view 0) <;> simp_all [advance]
  simp only [advance,active,deck,rule,stop,Option.map_some,Option.some.injEq,Config.mk.injEq,true_and]
  funext i
  exact SM.Action.apply_stay _

private def copying (old : I → Tape A) (k : ℕ) (w : List Bool) : Config A (Option Q) (Option I) :=
  ⟨none, deck (Function.update old src
    (Reset.atHead ((old src).pos + k) (old src).absolute))
    (Reset.atHead k (Uniform.Copy.written blank bit w k))⟩

private theorem at_source (T : Tape A) : Reset.atHead T.pos T.absolute = T := by
  cases T
  simp [Reset.atHead,Tape.absolute]

private theorem copy_zero (old : I → Tape A) (w : List Bool) :
    copying (Q := Q) src bit blank old 0 w =
      ⟨none,deck old (Tape.loaded blank [])⟩ := by
  simp only [copying,Nat.cast_zero,add_zero,at_source,Function.update_eq_self,Uniform.Copy.written_zero]
  congr 2
  change Tape.mk _ _ = Tape.mk _ _
  rw [Tape.mk.injEq]
  exact ⟨rfl,funext fun p => by cases p <;> rfl⟩

private theorem copy_step (old : I → Tape A) (w : List Bool)
    (read : ∀ j : ℕ, decode ((old src).view j) = w[j]?) (k : ℕ) (hk : k < w.length) :
    advance pub (copying src bit blank old k w) =
      some (copying src bit blank old (k+1) w) := by
  let D := copying (Q := Q) src bit blank old k w
  have src_read : decode ((D.tape (some src)).view 0) = some w[k] := by
    simpa [D,copying,deck,Reset.atHead,Tape.absolute,List.getElem?_eq_getElem hk] using read k
  change (rule m src decode bit none (fun i => (D.tape i).view 0)).map _ = _
  simp only [rule,src_read,Option.map_some,Option.some.injEq]
  change Config.mk _ _ = Config.mk _ _
  rw [Config.mk.injEq]
  refine ⟨rfl,?_⟩
  funext i
  cases i with
  | none =>
    change (Reset.atHead _ _).apply (bit w[k],.right) = Reset.atHead _ _
    rw [Reset.atHead_apply,Uniform.Copy.written_succ blank bit w k hk]
    simp [Move.shift]
  | some j =>
    by_cases eq : j=src
    · subst j
      simp only [D,copying,deck,Function.update_self,Reset.atHead,add_zero,ite_true]
      change (Reset.atHead _ _).apply ((old src).absolute ((old src).pos+k),.right) = Reset.atHead _ _
      rw [Reset.atHead_apply,Function.update_eq_self]
      simp [Move.shift,add_assoc]
    · simp only [D,copying,deck,Function.update_of_ne eq,ite_false,eq,SM.Action.apply_stay]

private theorem copy_full (old : I → Tape A) (w : List Bool)
    (read : ∀ j : ℕ, decode ((old src).view j) = w[j]?) :
    ∀ k ≤ w.length, Trace (advance pub) (copying src bit blank old 0 w) k
      (copying src bit blank old k w) := by
  intro k hk
  induction k with
  | zero => exact .nil _
  | succ k ih =>
    exact (ih (by omega)).trans (.single (copy_step m src decode bit blank old w read k (by omega)))

/-- The literal output tape starts blank at zero. This theorem includes
every step through the controller's terminal instruction and the copy. -/
theorem publish_run {x y : Config A Q I} {t : ℕ} (run : Trace (advance m) x t y)
    (stop : advance m y = none) (w : List Bool)
    (read : ∀ j : ℕ, decode ((y.tape src).view j) = w[j]?) :
    ∃ z, Trace (advance pub) (active blank x) (t+1+w.length) z ∧
      advance pub z = none ∧ whole blank (w.map bit) (z.tape none) := by
  have copy := copy_full m src decode bit blank y.tape w read w.length le_rfl
  rw [copy_zero] at copy
  refine ⟨_, ((lift_run m src decode bit blank run).trans
    (.single (handoff m src decode bit blank y stop))).trans copy, ?_, ?_⟩
  · simp [advance,rule,copying,deck,Reset.atHead,Tape.absolute,read]
  · funext i
    simp [copying,deck,Reset.atHead,Tape.absolute,Uniform.Copy.written_all,Uniform.Copy.rendering]

/-- During publication all old heads remain within one output length of
their controller endpoint, and the extra head starts at zero. -/
theorem publish_fence {x y : Config A Q I} {t H : ℕ}
    (run : FencedRun m (fun _ => -(H : ℤ)) (fun _ => (H : ℤ)) x t y)
    (stop : advance m y = none) (w : List Bool)
    (read : ∀ j : ℕ, decode ((y.tape src).view j) = w[j]?) :
    ∃ z, FencedRun pub (fun _ => -(H : ℤ)-w.length-1) (fun _ => (H : ℤ)+w.length+1)
        (active blank x) (t+1+w.length) z ∧
      advance pub z = none ∧ whole blank (w.map bit) (z.tape none) := by
  obtain ⟨z,all,halt,out⟩ := publish_run m src decode bit blank run.1 stop w read
  refine ⟨z,⟨all,?_⟩,halt,out⟩
  intro u hu v hv i
  have before {u v} (hu : u ≤ t) (hv : Trace (advance pub) (active blank x) u v)
      (i : Option I) : -(H : ℤ) ≤ (v.tape i).pos ∧ (v.tape i).pos ≤ H := by
    obtain ⟨old,pre,_⟩ := trace_split run.1 hu
    have eq := trace_endpoint_unique hv (lift_run m src decode bit blank pre)
    subst v
    cases i with
    | none => change -(H : ℤ) ≤ 0 ∧ 0 ≤ (H : ℤ); omega
    | some j => exact run.2 _ hu old pre j
  by_cases h : u ≤ t
  · have := before h hv i
    dsimp only
    omega
  · obtain ⟨mid,hpre,tail⟩ := trace_split hv (k := t) (by omega)
    have := before le_rfl hpre i
    have := head_excursion tail i
    dsimp only
    omega

/-- A fitting publication stays inside the original work strip. The only
moving heads are the source, which advances to one cell past its data, and
the fresh output, which advances from zero to the output length. -/
theorem publish_fixed_fence {x y : Config A Q I} {t H : ℕ}
    (run : FencedRun m (fun _ => -(H : ℤ)) (fun _ => (H : ℤ)) x t y)
    (stop : advance m y = none) (w : List Bool)
    (read : ∀ j : ℕ, decode ((y.tape src).view j) = w[j]?)
    (source_room : (y.tape src).pos + w.length ≤ (H : ℤ)) (output_room : w.length ≤ H) :
    ∃ z, FencedRun pub (fun _ => -(H : ℤ)) (fun _ => (H : ℤ))
        (active blank x) (t+1+w.length) z ∧
      advance pub z = none ∧ whole blank (w.map bit) (z.tape none) := by
  obtain ⟨z,all,halt,out⟩ := publish_run m src decode bit blank run.1 stop w read
  refine ⟨z,⟨all,?_⟩,halt,out⟩
  intro u hu v hv i
  by_cases early : u ≤ t
  · obtain ⟨old,pre,_⟩ := trace_split run.1 early
    rw [trace_endpoint_unique hv (lift_run m src decode bit blank pre)]
    cases i with
    | some j => exact run.2 u early old pre j
    | none =>
      change -(H : ℤ) ≤ 0 ∧ 0 ≤ (H : ℤ)
      omega
  · let k := u-(t+1)
    have bound : k ≤ w.length := by dsimp [k]; omega
    have start := (lift_run m src decode bit blank run.1).trans
      (.single (handoff m src decode bit blank y stop))
    have scan := copy_full m src decode bit blank y.tape w read k bound
    rw [copy_zero] at scan
    have total := start.trans scan
    rw [show t+1+k=u by dsimp [k]; omega] at total
    rw [trace_endpoint_unique hv total]
    cases i with
    | none =>
      change -(H : ℤ) ≤ (k : ℤ) ∧ (k : ℤ) ≤ H
      omega
    | some j =>
      have before := run.2 t le_rfl y run.1 j
      dsimp only at before
      by_cases eq : j=src
      · subst j
        simp only [copying,deck,Function.update_self,Reset.atHead]
        omega
      · simpa only [copying,deck,Function.update_of_ne eq] using before

end StagingPublish

end NearSquareRoot
end Computability
end OAI
