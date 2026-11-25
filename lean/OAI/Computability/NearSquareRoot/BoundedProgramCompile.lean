import OAI.Computability.NearSquareRoot.BoundedProgram
import OAI.Computability.NearSquareRoot.ScheduleSchoolSegments
import OAI.Computability.NearSquareRoot.ScheduleSchoolRelease
import OAI.Computability.IntegerMultiplication.Prog.Compile
import Batteries.Tactic.OpenPrivate

/-!
# Live stack heights in the compiled structured program

The data registers and the compiler's return-address stack are separate stacks.
Their heights are therefore combined by a maximum. Each bound holds at every
prefix of the actual execution, including the two administrative steps of a join.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Space

open IntegerMultiplication IntegerMultiplication.Prog Schoolbook

open private pc ix next next_do ret_step pc_good touched_mem update from
  OAI.Computability.IntegerMultiplication.Prog.Compile
open private stack_growth from OAI.Computability.NearSquareRoot.ScheduleSchoolSegments

private theorem one_segment {A Q I : Type} {m : SM.Rule A Q I} {x y : SM.Config A Q I}
    {B : ℕ} (run : Trace (SM.advance m) x 1 y) (hx : ∀ i, (x.stack i).length ≤ B)
    (hy : ∀ i, (y.stack i).length ≤ B) : Segment m x 1 y B := by
  refine ⟨run, fun {j u} hj sub i => ?_⟩
  rcases show j = 0 ∨ j = 1 by omega with rfl | rfl
  · rw [trace_endpoint_unique sub (.nil x)]
    exact hx i
  · rw [trace_endpoint_unique sub run]
    exact hy i

private theorem prepend {A Q I : Type} {m : SM.Rule A Q I} {x y z : SM.Config A Q I}
    {n B : ℕ} (step : SM.advance m x = some y) (hx : ∀ i, (x.stack i).length ≤ B)
    (tail : Segment m y n z B) : Segment m x (1 + n) z B :=
  (one_segment (Trace.single step) hx (tail.height (Nat.zero_le _) (.nil y))).trans tail

variable {A : Type} [Fintype A] (U : List (Loc A))

omit [Fintype A] in
private theorem machine_height (q : Pc U) (r : Reg A) (k : List (Ptr U))
    {cap B : ℕ} (data : ∀ i, (r i).length ≤ cap) (hc : cap ≤ B) (hk : k.length ≤ B) :
    ∀ i, ((machine U q r k).stack i).length ≤ B := by
  intro i
  cases i with
  | none => simpa only [machine, List.length_map] using hk
  | some j => simpa only [machine, List.length_map] using (data j.val).trans hc

private theorem primitive {cap depth : ℕ} {Γ : Scope A} {c : Prog A} {r s : Reg A}
    (run : Prog.Run Γ c r 1 s) (start : ∀ i, (r i).length ≤ cap) (stop : ∀ i, (s i).length ≤ cap)
    (hg : Good U Γ c) (ha : Above U Γ) (k : List (Ptr U)) :
    Segment (compile U) (machine U (pc U Γ c) r k) 1 (machine U none s k)
      (max cap (k.length + depth)) :=
  one_segment (run.compile_ok U hg ha k)
    (machine_height U _ _ _ start (Nat.le_max_left ..) (by omega))
    (machine_height U _ _ _ stop (Nat.le_max_left ..) (by omega))

private theorem compile_segment_aux {cap depth : ℕ} {Γ : Scope A} {c : Prog A}
    {r s : Reg A} {n : ℕ} (h : BoundedRun cap depth Γ c r n s)
    (hg : Good U Γ c) (ha : Above U Γ) (k : List (Ptr U)) :
    Segment (compile U) (machine U (pc U Γ c) r k) n (machine U none s k)
      (max cap (k.length + depth)) := by
  classical
  induction h generalizing k with
  | @clock depth Γ c r n s run data ret =>
    refine ⟨run.compile_ok U hg ha k, fun {j u} hj sub i => ?_⟩
    have growth := stack_growth sub i
    cases i with
    | none =>
      simp only [machine, List.length_map] at growth
      exact growth.trans ((Nat.add_le_add_left (hj.trans ret) _).trans (Nat.le_max_right ..))
    | some l =>
      simp only [machine, List.length_map] at growth
      exact growth.trans (((Nat.add_le_add_left hj _).trans (data l.val)).trans (Nat.le_max_left ..))
  | pass data => exact primitive U .pass data data hg ha k
  | @pop depth Γ i r data =>
    apply primitive U .pop data _ hg ha k
    intro j
    by_cases eq : j = i
    · subst j
      simp only [Function.update_self, List.length_tail]
      have := data i
      omega
    · simpa only [Function.update_of_ne eq] using data j
  | @push depth Γ i v r data =>
    exact primitive U .push (BoundedRun.start (BoundedRun.push (depth := depth) (Γ := Γ) data)) data hg ha k
  | @look depth Γ i f r n s child ih =>
    have hchild (o : Option A) : Good U Γ (f o) := by
      intro l hl
      apply hg
      rw [sites]
      exact List.mem_cons.mpr (Or.inr (List.mem_flatMap.mpr ⟨o, mem_options o, hl⟩))
    apply prepend (y := machine U (pc U Γ (f (r i).head?)) r k)
    · rw [pc_good U hg]
      apply next U
      have hi := touched_mem U Γ (.look i f) (hg (sites_self _ _))
      change i ∈ used U at hi
      have e := ix_val U i hi
      dsimp [compile, machine, SM.tops]
      cases hlist : r i <;> simp [e, hlist]
    · exact machine_height U _ _ _ child.start (Nat.le_max_left ..) (by omega)
    · exact ih (hchild _) ha k
  | @join depth leftDepth Γ c d r n s m t left right reserve ih jh =>
    have hc : Good U Γ c := by
      intro l hl
      apply hg
      rw [sites]
      simp [hl]
    have hd : Good U Γ d := by
      intro l hl
      apply hg
      rw [sites]
      simp [hl]
    let p : Ptr U := ⟨(Γ,d), hd (sites_self _ _)⟩
    have ep : pc U Γ d = some p := pc_good U hd
    have first := (ih hc ha (p :: k)).mono (H' := max cap (k.length + depth)) (by
      simp only [List.length_cons]
      omega)
    have last := jh hd ha k
    have enter : SM.advance (compile U) (machine U (pc U Γ (.join c d)) r k) =
        some (machine U (pc U Γ c) r (p :: k)) := by
      rw [pc_good U hg]
      apply next_do U _ _ _ _ k (p::k) none (.push (.inr p)) (g := compile U)
      · dsimp [compile, machine, SM.tops]
        rw [ep]
        rfl
      · intro l
        cases l <;> simp [machine, update, SM.Action.perform, Function.update_of_ne]
    have front := prepend enter (machine_height U _ _ _ left.start (Nat.le_max_left ..) (by omega)) first
    have ret := one_segment (Trace.single (ret_step U s p k)) (first.height (by rfl) first.run)
      (machine_height U _ _ _ right.start (Nat.le_max_left ..) (by omega))
    rw [ep] at last
    exact (front.trans ret).trans last
  | @tie depth Γ c r n s child ih =>
    have hc : Good U (c :: Γ) c := by
      intro l hl
      apply hg
      rw [sites]
      simp [hl]
    have he : Above U (c :: Γ) := by
      intro i a hlookup
      cases i with
      | zero =>
        obtain rfl : c = a := by simpa using hlookup
        exact hc
      | succ j => simpa using ha j a (by simpa using hlookup)
    apply prepend (tail := ih hc he k)
    · rw [pc_good U hg]
      exact next U _ _ _ _ rfl
    · exact machine_height U _ _ _ child.start (Nat.le_max_left ..) (by omega)
  | @again depth Γ i c r n s lookup child ih =>
    have above : Above U (Γ.drop i) := by
      intro j d e
      simp only [List.getElem?_drop] at e
      simpa [List.drop_drop, add_comm] using ha _ _ e
    apply prepend (tail := ih (ha _ _ lookup) above k)
    · rw [pc_good U hg]
      apply next U
      simp [compile, lookup]
    · exact machine_height U _ _ _ child.start (Nat.le_max_left ..) (by omega)

/-- Compile a space-certified run in any enclosing compilation unit, with an
arbitrary incoming return stack. The cap counts the heights of compiler stacks
after each transition, including both endpoints. -/
theorem BoundedRun.compile_segment {cap depth : ℕ} {Γ : Scope A} {c : Prog A}
    {r s : Reg A} {n : ℕ} (h : BoundedRun cap depth Γ c r n s)
    (hg : Good U Γ c) (ha : Above U Γ) (k : List (Ptr U)) :
    Segment (compile U) (machine U (some ⟨(Γ,c), hg (sites_self c Γ)⟩) r k) n
      (machine U none s k) (max cap (k.length + depth)) := by
  simpa only [pc_good U hg] using compile_segment_aux U h hg ha k

/-- Release one closed program to one fixed deterministic finite multitape machine.
The clock includes every step of the final physical output copy. The
visited-cell constant is independent of the input, time, and space certificates. -/
theorem bounded_release_indexed {A : Type} [Fintype A] (p : Prog A) :
    let I := Option (Ix (sites [] p))
    ∃ (X Q : Type) (_ : Finite X) (_ : Finite Q) (_ : Finite I)
      (sym : A → X) (blank : X) (inp out : I) (start : Q) (m : TM.Rule X Q I) (K : ℕ),
      Function.Injective sym ∧ (∀ a, sym a ≠ blank) ∧ inp ≠ out ∧
      ∀ (input : List A) (r : Reg A) (n cap depth : ℕ),
        BoundedRun cap depth [] p (fun i => if i = 0 then input else []) n r →
        ∃ (load : I → TM.Tape X) (done : TM.Config X Q I),
          load inp = TM.Tape.loaded blank (input.map sym) ∧
          (∀ i, i ≠ inp → load i = TM.Tape.loaded blank []) ∧
          Trace (TM.advance m) ⟨start, load⟩ (2 * n + 1 + (r 0).length) done ∧
          TM.advance m done = none ∧ TM.whole blank ((r 0).map sym) (done.tape out) ∧
          VisitsAtMost m ⟨start, load⟩ (2 * n + 1 + (r 0).length)
            (K * (4 * max cap depth + 5)) := by
  classical
  let area := sites [] p
  let : Fintype (Ptr area) := Fintype.subtype area.toFinset (by simp)
  let : Fintype (Idx area) := Fintype.subtype (used area).toFinset (by simp)
  have good : Good area [] p := fun _ h => h
  let entry : Pc area := some ⟨([],p), good (sites_self p [])⟩
  let zeroReg : Ix area := some (ix area 0)
  have hz := ix_val area 0 (by simp [used])
  refine ⟨Option (Sym area), Option (SM.PC (Sym area) (Pc area) (Ix area)),
    inferInstance, inferInstance, inferInstance, fun a => some (.inl a), none, some zeroReg,
    none, some (Sum.inl entry), SM.complete zeroReg (compile area), Fintype.card (Option (Ix area)),
    fun a b e => by simpa using e, by simp, by simp, ?_⟩
  intro input r n cap depth run
  have seg := run.compile_segment area good (fun i => by simp) []
  change Segment (compile area) (machine area entry _ []) n (machine area none r [])
    (max cap (([] : List (Ptr area)).length + depth)) at seg
  have origin : machine area entry (fun i => if i = 0 then input else []) [] =
      SM.origin entry zeroReg (input.map Sum.inl) := by
    unfold machine SM.origin
    congr 1
    funext l
    cases l with
    | none => simp [zeroReg]
    | some j =>
      by_cases h : j = ix area 0
      · subst j
        simp [hz, zeroReg]
      · have hj : j.val ≠ 0 := fun e => h (Subtype.ext (e.trans hz.symm))
        simp [hj, h, zeroReg]
  rw [origin] at seg
  simp only [List.length_nil, Nat.zero_add] at seg
  have halted : SM.advance (compile area) (machine area none r []) = none := rfl
  obtain ⟨done, execution, stopped, written, visits⟩ :=
    complete_run_space (k := zeroReg) seg.run halted seg.height
  have contents : (machine area none r []).stack zeroReg = (r 0).map Sum.inl := by
    simp [machine, zeroReg, hz]
  rw [contents, List.length_map] at execution visits
  rw [contents, List.map_map] at written
  refine ⟨fun i => if i = some zeroReg then TM.Tape.loaded none ((input.map Sum.inl).map some)
      else TM.Tape.loaded none [], done, ?_, ?_, execution, stopped, written, visits⟩
  · simp [Function.comp_def]
  · intro i h
    simp [h]

/-- Existential tape-index form of the physical release. -/
theorem bounded_release {A : Type} [Fintype A] (p : Prog A) :
    ∃ (X Q I : Type) (_ : Finite X) (_ : Finite Q) (_ : Finite I)
      (sym : A → X) (blank : X) (inp out : I) (start : Q) (m : TM.Rule X Q I) (K : ℕ),
      Function.Injective sym ∧ (∀ a, sym a ≠ blank) ∧ inp ≠ out ∧
      ∀ (input : List A) (r : Reg A) (n cap depth : ℕ),
        BoundedRun cap depth [] p (fun i => if i = 0 then input else []) n r →
        ∃ (load : I → TM.Tape X) (done : TM.Config X Q I),
          load inp = TM.Tape.loaded blank (input.map sym) ∧
          (∀ i, i ≠ inp → load i = TM.Tape.loaded blank []) ∧
          Trace (TM.advance m) ⟨start, load⟩ (2 * n + 1 + (r 0).length) done ∧
          TM.advance m done = none ∧ TM.whole blank ((r 0).map sym) (done.tape out) ∧
          VisitsAtMost m ⟨start, load⟩ (2 * n + 1 + (r 0).length)
            (K * (4 * max cap depth + 5)) := by
  obtain ⟨X,Q,hX,hQ,hI,sym,blank,inp,out,start,m,K,proof⟩ := bounded_release_indexed p
  exact ⟨X,Q,Option (Ix (sites [] p)),hX,hQ,hI,sym,blank,inp,out,start,m,K,proof⟩

end Space

end NearSquareRoot
end Computability
end OAI
