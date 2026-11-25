import OAI.Computability.NearSquareRoot.ScheduleProgramLoad
import OAI.Computability.NearSquareRoot.ScheduleUniversalRun
import OAI.Computability.NearSquareRoot.InterchangeSplitCompose

/-!
# Duplicating the generated interpreter table

Both ROM heads start at cell zero. The loader copies all tags simultaneously to the
second tape, recognizes the first data-side blank, and rewinds to the origin tag.
On return the source head advances to the first row, and the duplicate stays at zero.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Universal.Loader

open IntegerMultiplication TM
variable {A I : Type}

inductive Control where
  | copy | rewind | done
  deriving DecidableEq

instance : Finite Control := Finite.of_injective
  (fun q : Control => match q with | .copy => (0 : Fin 3) | .rewind => 1 | .done => 2)
  (by intro x y h; cases x <;> cases y <;> simp_all)

private def issue (v : Index I → Letter A I) (ctrl : Control) (m n : Move)
    (next : Letter A I) : Option (Control × (Index I → Letter A I × Move)) :=
  some (ctrl, fun
    | .inl i => (v (.inl i), .stay)
    | .inr false => (v (.inr false), m)
    | .inr true => (next, n))

/-- The same three states load every finite program table. -/
def rule : Rule (Letter A I) Control (Index I)
  | .copy, v =>
    match v (.inr false) with
    | .inr tag => issue v .copy .right .right (.inr tag)
    | .inl _ => issue v .rewind .stay .stay (v (.inr true))
  | .rewind, v =>
    match v (.inr false) with
    | .inr .origin => issue v .done .right .stay (v (.inr true))
    | _ => issue v .rewind .left .left (v (.inr true))
  | .done, _ => none

private def absoluteWord (blank : A) (code : List (Tag A I)) : ℤ → Letter A I :=
  (Tape.loaded (.inl blank) (code.map Sum.inr)).view

private def atPos {X : Type} (f : ℤ → X) (p : ℤ) : Tape X := ⟨p, fun k => f (p+k)⟩

private theorem atPos_move {X : Type} (f : ℤ → X) (p : ℤ) (m : Move) :
    (atPos f p).apply (f p,m) = atPos f (p+m.shift) := by
  simp only [atPos,Tape.apply,Tape.mk.injEq,true_and]
  funext k
  split
  · rename_i h; congr 1; omega
  · congr 1; omega

private theorem data_stay (d : Tape A) :
    (dataCell (I := I) d).apply ((dataCell d).view 0,.stay) = dataCell d := by
  simp only [dataCell,Tape.apply,Move.shift,add_zero,Tape.mk.injEq,true_and]
  funext k
  split <;> simp_all

private def copied (blank : A) (code : List (Tag A I)) (k : ℕ) : ℤ → Letter A I :=
  fun z => if z < k then absoluteWord blank code z else .inl blank

private theorem write_copied (blank : A) (code : List (Tag A I)) (k : ℕ) :
    (atPos (copied blank code k) k).apply (absoluteWord blank code k,.right) =
      atPos (copied blank code (k+1)) (k+1) := by
  simp only [Tape.apply,atPos,Move.shift,Tape.mk.injEq,true_and,copied,Nat.cast_add,Nat.cast_one]
  funext i
  change (if i+1=0 then absoluteWord blank code k else
    if (k:ℤ)+(i+1)<k then absoluteWord blank code (k+(i+1)) else Sum.inl blank) =
    if (k:ℤ)+1+i<k+1 then absoluteWord blank code (k+1+i) else Sum.inl blank
  by_cases h : i+1=0
  · rw [ite_eq_left h,ite_eq_left (by omega),show (k:ℤ)+1+i = k by omega]
  · rw [ite_eq_right h,show (k:ℤ)+(i+1)=k+1+i by omega]
    by_cases l : (k:ℤ)+1+i < k
    · rw [ite_eq_left l,ite_eq_left (by omega)]
    · rw [ite_eq_right l,ite_eq_right (by omega)]

private theorem copied_full (blank : A) (code : List (Tag A I)) :
    copied blank code code.length = absoluteWord blank code := by
  funext z
  unfold copied
  split
  · rfl
  · rename_i h
    cases z with
    | negSucc r => omega
    | ofNat r =>
      change ¬(r:ℤ) < code.length at h
      have hr : code.length ≤ r := by omega
      simp [absoluteWord,Tape.loaded,List.getElem?_eq_none hr]

private theorem copied_zero (blank : A) (code : List (Tag A I)) :
    copied blank code 0 = absoluteWord blank ([] : List (Tag A I)) := by
  funext z
  cases z <;> simp [copied,absoluteWord,Tape.loaded]

/-- Configuration with data heads frozen and independently positioned ROM heads. -/
def state (ctrl : Control) (d : I → Tape A) (src dst : Tape (Letter A I)) :
    Config (Letter A I) Control (Index I) :=
  ⟨ctrl, fun
    | .inl i => dataCell (d i)
    | .inr false => src
    | .inr true => dst⟩

private def forward (blank : A) (code : List (Tag A I)) (d : I → Tape A) (k : ℕ) :=
  state .copy d (romWord blank code k) (atPos (copied blank code k) k)

private def backward (blank : A) (code : List (Tag A I)) (d : I → Tape A) (k : ℕ) :=
  state .rewind d (romWord blank code k) (romWord blank code k)

/-- Single generated table on the source, entirely blank second program tape. -/
def initial (blank : A) (code : List (Tag A I)) (d : I → Tape A) :=
  state .copy d (romWord blank code 0) (romWord blank [] 0)

/-- The source head is at the first row, the other head is ready for a jump. -/
def ready (blank : A) (code : List (Tag A I)) (d : I → Tape A) :=
  state .done d (romWord blank code 1) (romWord blank code 0)

@[simp] theorem ready_tapes (blank : A) (code : List (Tag A I)) (d : I → Tape A) :
    (ready blank code d).tape = (loadedConf blank code d false .seek 1 0).tape := by
  funext i
  cases i with
  | inl j => rfl
  | inr j => cases j <;> rfl

private theorem step {q q' : Control} {d : I → Tape A} {s t s' t' : Tape (Letter A I)}
    {ms mt : Move} {write : Letter A I}
    (h : let v := fun i => ((state q d s t).tape i).view 0
      rule q v = issue v q' ms mt write)
    (hs : s.apply (s.view 0,ms) = s') (ht : t.apply (write,mt) = t') :
    advance rule (state q d s t) = some (state q' d s' t') := by
  change Option.map _ (rule q _) = _
  rw [h]
  simp only [issue,Option.map_some,Option.some.injEq]
  apply congrArg (Config.mk q')
  funext i
  cases i with
  | inl j => exact data_stay (d j)
  | inr j => cases j <;> assumption

private theorem word_move (blank : A) (code : List (Tag A I)) (k : ℤ) (m : Move) :
    (romWord blank code k).apply ((romWord blank code k).view 0,m) =
      romWord blank code (k+m.shift) := by
  simpa only [romWord,absoluteWord,atPos,add_zero] using atPos_move (absoluteWord blank code) k m

private theorem copy_one (blank : A) (code : List (Tag A I)) (d : I → Tape A)
    (k : ℕ) (hk : k < code.length) :
    advance rule (forward blank code d k) = some (forward blank code d (k+1)) := by
  have read : (romWord blank code k).view 0 = .inr code[k] := by
    simp [romWord,Tape.loaded,List.getElem?_eq_getElem hk]
  apply step (ms := .right) (mt := .right) (write := .inr code[k])
  · dsimp only [rule, state]
    rw [read]
  · simpa only [Move.shift,Nat.cast_add,Nat.cast_one] using word_move blank code k .right
  · have same : absoluteWord blank code k = .inr code[k] := by
      simpa only [romWord,absoluteWord,add_zero] using read
    simpa only [same,Nat.cast_add,Nat.cast_one] using write_copied blank code k

private theorem copy_turn (blank : A) (code : List (Tag A I)) (d : I → Tape A) :
    advance rule (forward blank code d code.length) = some (backward blank code d code.length) := by
  have read : (romWord blank code code.length).view 0 = .inl blank := by
    simp [romWord,Tape.loaded]
  unfold forward
  rw [copied_full]
  change advance rule (state .copy d (romWord blank code code.length) (romWord blank code code.length)) = _
  apply step (ms := .stay) (mt := .stay)
    (write := (romWord blank code code.length).view 0)
  · dsimp only [rule,state]
    rw [read]
  · simpa only [Move.shift,add_zero] using word_move blank code code.length .stay
  · simpa only [Move.shift,add_zero] using word_move blank code code.length .stay

private theorem rewind_one (blank : A) (code : List (Tag A I)) (d : I → Tape A)
    (k : ℕ) (h : fetch code (k+1 : ℕ) ≠ .origin) :
    advance rule (backward blank code d (k+1)) = some (backward blank code d k) := by
  have hne : (romWord blank code (↑(k+1 : ℕ))).view 0 ≠ .inr .origin := by
    intro e
    apply h
    change ((code.map Sum.inr)[k+1]?).getD (.inl blank) = .inr .origin at e
    rw [List.getElem?_map] at e
    change code[k+1]?.getD .endCode = .origin
    cases he : code[k+1]? <;> simp_all only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some, Sum.inr.injEq, reduceCtorEq]
  apply step (ms := .left) (mt := .left) (write := (romWord blank code (↑(k+1 : ℕ))).view 0)
  · dsimp only [rule,state]
    cases he : (romWord blank code (↑(k+1 : ℕ))).view 0 with
    | inl x => rfl
    | inr tag => cases tag <;> first | rfl | exact (hne he).elim
  · convert word_move blank code (↑(k+1 : ℕ)) .left using 1
    simp [Move.shift]
  · convert word_move blank code (↑(k+1 : ℕ)) .left using 1
    simp [Move.shift]

private theorem rewind_end (blank : A) (code : List (Tag A I)) (d : I → Tape A)
    (h : code.head? = some .origin) :
    advance rule (backward blank code d 0) = some (ready blank code d) := by
  have read : (romWord blank code 0).view 0 = .inr .origin := by
    cases code <;> simp_all [romWord,Tape.loaded]
  apply step (ms := .right) (mt := .stay) (write := (romWord blank code 0).view 0)
  · have read' : (romWord blank code (↑(0 : ℕ))).view 0 = .inr .origin := read
    dsimp only [rule,state]
    rw [read', read]
  · exact word_move blank code 0 .right
  · exact word_move blank code 0 .stay


/-- On data tapes the fence consists of the original head cell. On each
ROM tape it includes displacements from zero through the first blank. -/
def bound (d : I → Tape A) (romBound : ℕ) : Index I → ℤ
  | .inl i => (d i).pos
  | .inr _ => romBound

private def safe (d : I → Tape A) (l : ℕ) (x : Config (Letter A I) Control (Index I)) :=
  ∀ i, bound d 0 i ≤ (x.tape i).pos ∧ (x.tape i).pos ≤ bound d l i

private theorem safe_state (q : Control) (d : I → Tape A) (l : ℕ)
    (s t : Tape (Letter A I)) (hs : 0 ≤ s.pos ∧ s.pos ≤ l) (ht : 0 ≤ t.pos ∧ t.pos ≤ l) :
    safe d l (state q d s t) := by
  intro i
  cases i with
  | inl i => exact ⟨le_rfl,le_rfl⟩
  | inr i => cases i <;> assumption

private theorem single {d : I → Tape A} {l : ℕ} {x y : Config (Letter A I) Control (Index I)}
    (s : advance rule x = some y) (hx : safe d l x) (hy : safe d l y) :
    FencedRun rule (bound d 0) (bound d l) x 1 y := by
  refine ⟨Trace.single s, fun u hu z hz => ?_⟩
  rcases (show u=0 ∨ u=1 by omega) with rfl | rfl
  · have eq := trace_endpoint_unique hz (.nil x)
    exact eq ▸ hx
  · have eq := trace_endpoint_unique hz (Trace.single s)
    exact eq ▸ hy

private theorem empty {d : I → Tape A} {l : ℕ} {x : Config (Letter A I) Control (Index I)}
    (hx : safe d l x) : FencedRun rule (bound d 0) (bound d l) x 0 x := by
  refine ⟨.nil _,fun u hu z hz => ?_⟩
  have h : u=0 := by omega
  subst u
  exact (trace_endpoint_unique hz (.nil x)) ▸ hx

private theorem safe_forward (blank : A) (code : List (Tag A I)) (d : I → Tape A)
    (k : ℕ) (hk : k ≤ code.length) : safe d code.length (forward blank code d k) :=
  safe_state _ _ _ _ _ ⟨Int.natCast_nonneg _, by change (k:ℤ) ≤ code.length; exact_mod_cast hk⟩
    ⟨Int.natCast_nonneg _, by change (k:ℤ) ≤ code.length; exact_mod_cast hk⟩

private theorem safe_backward (blank : A) (code : List (Tag A I)) (d : I → Tape A)
    (k : ℕ) (hk : k ≤ code.length) : safe d code.length (backward blank code d k) :=
  safe_state _ _ _ _ _ ⟨Int.natCast_nonneg _, by change (k:ℤ) ≤ code.length; exact_mod_cast hk⟩
    ⟨Int.natCast_nonneg _, by change (k:ℤ) ≤ code.length; exact_mod_cast hk⟩

private theorem copy_run (blank : A) (code : List (Tag A I)) (d : I → Tape A)
    (k : ℕ) (hk : k ≤ code.length) :
    FencedRun rule (bound d 0) (bound d code.length)
      (forward blank code d 0) k (forward blank code d k) := by
  induction k with
  | zero => exact empty (safe_forward _ _ _ _ hk)
  | succ k ih =>
    exact (ih (by omega)).trans (single (copy_one blank code d k (by omega))
      (safe_forward _ _ _ _ (by omega)) (safe_forward _ _ _ _ hk))

private theorem rewind_run (blank : A) (code : List (Tag A I)) (d : I → Tape A)
    (hn : ∀ k : ℕ, 0 < k → fetch code k ≠ .origin) (k : ℕ) (hk : k ≤ code.length) :
    FencedRun rule (bound d 0) (bound d code.length)
      (backward blank code d k) k (backward blank code d 0) := by
  induction k with
  | zero => exact empty (safe_backward _ _ _ _ hk)
  | succ k ih =>
    simpa only [Nat.add_comm 1 k] using
      (single (rewind_one blank code d k (hn _ (by omega)))
        (safe_backward _ _ _ _ hk) (safe_backward _ _ _ _ (by omega))).trans (ih (by omega))

/-- Complete two-ROM installation with all physical moves and a simultaneous
bound on the heads in every prefix. `rule` is independent of the table size. -/
theorem load (blank : A) (code : List (Tag A I)) (d : I → Tape A)
    (h0 : code.head? = some .origin) (hn : ∀ k : ℕ, 0 < k → fetch code k ≠ .origin) :
    FencedRun rule (bound d 0) (bound d code.length)
      (initial blank code d) (2 * code.length + 2) (ready blank code d) := by
  have hlen : 1 ≤ code.length := by cases code <;> simp_all
  have first := copy_run blank code d code.length le_rfl
  have turn := single (copy_turn blank code d)
    (safe_forward _ _ _ _ le_rfl) (safe_backward _ _ _ _ le_rfl)
  have back := rewind_run blank code d hn code.length le_rfl
  have finish := single (rewind_end blank code d h0) (safe_backward _ _ _ _ (by omega))
    (safe_state _ _ _ _ _ (show (0:ℤ) ≤ 1 ∧ (1:ℤ) ≤ code.length from
      ⟨by decide, by exact_mod_cast hlen⟩)
      (show (0:ℤ) ≤ 0 ∧ (0:ℤ) ≤ code.length from ⟨le_rfl,Int.natCast_nonneg _⟩))
  have h := (((first.trans turn).trans back).trans finish)
  have init : forward blank code d 0 = initial blank code d := by
    simp only [forward,initial,copied_zero]
    rfl
  rwa [init,show code.length+1+code.length+1=2*code.length+2 by omega] at h

theorem load_program {m : ℕ} (blank : A) (machine : Rule A (Fin m) I)
    (rs : List (I → A)) (d : I → Tape A) :
    let code := program machine rs
    FencedRun rule (bound d 0) (bound d code.length)
      (initial blank code d) (2 * code.length + 2) (ready blank code d) :=
  load blank _ d rfl (fetch_no_origin machine rs)


/-- The control that loads one generated table and immediately interprets it. -/
noncomputable def installAndRun [Finite A] [Finite I] (blank : A) :
    Rule (Letter A I) (Control ⊕ PC) (Index I) :=
  TapeSequence.rule rule (Universal.rule blank) (false,.seek)

/-- Run a candidate from state zero after producing its second table copy.
The bound includes the loader, the transition that switches control, every
simulated step, and the search for the final halting branch. -/
theorem install_halting_trace [Finite A] [Finite I] {m : ℕ} (hm : 0 < m)
    (blank : A) (machine : Rule A (Fin m) I) (rs : List (I → A))
    (complete : ∀ r, r ∈ rs) (d : I → Tape A) {z : Config A (Fin m) I} {t : ℕ}
    (run : Trace (advance machine) ⟨⟨0,hm⟩,d⟩ t z) (halt : advance machine z = none) :
    let code := program machine rs
    ∃ n finish, n ≤ 2*code.length+3 + 4*(code.length+1)*(t+1) ∧
      Trace (advance (installAndRun blank)) (TapeSequence.relabel Sum.inl (initial blank code d))
        n finish ∧ advance (installAndRun blank) finish = none ∧
      ∀ i, finish.tape (.inl i) = dataCell (z.tape i) := by
  let code := program machine rs
  have loadRun := (load_program blank machine rs d).1
  obtain ⟨u,y,hu,hr,hy,hd⟩ := interpret_halting_trace blank machine rs complete run halt false
  have start : Universal.ready machine rs false ⟨⟨0,hm⟩,d⟩ =
      normalize (loadedConf blank code d false .seek 1 0) := by
    simp [Universal.ready,normalize_loaded,code]
  rw [start] at hr
  obtain ⟨w,hw,e⟩ := pull_trace hr
  have hh := pull_halt (c := w) (by rw [e]; exact hy)
  have hentry : (⟨(false,.seek),(ready blank code d).tape⟩ :
      Config (Letter A I) PC (Index I)) = loadedConf blank code d false .seek 1 0 := by
    rw [ready_tapes]
    rfl
  rw [← hentry] at hw
  obtain ⟨tr,st⟩ := TapeSequence.run rule (Universal.rule blank) (false,.seek)
    loadRun (by rfl) hw hh
  refine ⟨_,_,?_,tr,st,?_⟩
  · omega
  · intro i
    change w.tape (.inl i) = _
    rw [← normalize_data w i,e,hd]

end Universal.Loader

end NearSquareRoot
end Computability
end OAI
