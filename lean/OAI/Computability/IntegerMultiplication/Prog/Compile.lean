import OAI.Computability.IntegerMultiplication.TMProgram
import OAI.Computability.IntegerMultiplication.SM.Output
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.List
import Mathlib.Tactic.FinCases

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Prog

variable {A : Type} [Fintype A]

abbrev Loc (A : Type) := Scope A × Prog A

noncomputable def options : List (Option A) := Finset.univ.toList

@[simp]
theorem mem_options (o : Option A) : o ∈ options := by simp [options]

/-- All program points used in a compilation. -/
noncomputable def sites (Γ : Scope A) (c : Prog A) : List (Loc A) :=
  (Γ,c) :: match c with
  | .pass | .push _ _ | .pop _ | .again _ => []
  | .look _ f => options.flatMap (fun x => sites Γ (f x))
  | .join a b => sites Γ a ++ sites Γ b
  | .tie b => sites (b::Γ) b
termination_by structural c

theorem sites_self (c : Prog A) (Γ) : (Γ,c) ∈ sites Γ c := by rw [sites.eq_def]; simp

variable (U : List (Loc A))

/-- Register 0 always present for the final interface. -/
def touched : Prog A → ℕ
  | .push i _ | .pop i | .look i _ => i
  | _ => 0

def used : List ℕ := 0 :: U.map (fun p => touched p.2)

abbrev Ptr := {p : Loc A // p ∈ U}
abbrev Idx := {i : ℕ // i ∈ used U}

/-- None in the pc type = return; none in stack index type = return-address stack. -/
abbrev Pc := Option (Ptr U)
abbrev Ix := Option (Idx U)
abbrev Sym := Sum A (Ptr U)

section
open Classical
private noncomputable def pc (Γ : Scope A) (c : Prog A) : Pc U :=
  if h : (Γ,c) ∈ U then some ⟨(Γ,c),h⟩ else none

private def ix (i : ℕ) : Idx U :=
  if h : i ∈ used U then ⟨i,h⟩ else ⟨0, by simp [used]⟩

omit [Fintype A] in
theorem ix_val (i) (h : i ∈ used U) : (ix U i).val = i := by simp [ix, h]

omit [Fintype A] in
private theorem touched_mem (Γ c) (h : (Γ,c) ∈ U) : touched c ∈ used U := by
  simp only [used, List.mem_cons, List.mem_map]
  exact Or.inr ⟨(Γ,c), h, rfl⟩

noncomputable def compile : SM.Rule (Sym U) (Pc U) (Ix U) :=
  let go (q : Pc U) : Option ((Pc U) × ((Ix U) → SM.Action (Sym U))) :=
    some (q, fun _ => .skip)
  let act (k : Ix U) (a : SM.Action (Sym U)) (q : Pc U) :=
    some (q, Function.update (fun (_ : Ix U) => (SM.Action.skip : SM.Action (Sym U))) k a)
  fun q stk => match q with
  | none =>
    match stk none with
    | some (.inr p) => act none .pop (some p)
    | _ => none
  | some p =>
    let Γ := p.val.1; match p.val.2 with
    | .pass => go none
    | .push i v => act (some (ix U i)) (.push (.inl v)) none
    | .pop i => act (some (ix U i)) .pop none
    | .look i f =>
      match stk (some (ix U i)) with
      | none => go (pc U Γ (f none))
      | some (.inl v) => go (pc U Γ (f (some v)))
      | _ => none
    | .join a b =>
      match pc U Γ b with
      | none => none
      | some p' => act none (.push (.inr p')) (pc U Γ a)
    | .tie a => go (pc U (a::Γ) a)
    | .again i =>
      match Γ[i]? with
      | some a => go (pc U (Γ.drop i) a)
      | none => none
end

def machine (q : Pc U) (r : Reg A) (c : List (Ptr U)) : SM.Config (Sym U) (Pc U) (Ix U) :=
  ⟨q, fun
    | none => c.map Sum.inr
    | some i => (r i.val).map Sum.inl⟩

-- Helpers for proofs of step rules.
omit [Fintype A] in
private theorem next (q : Pc U) (q' : Pc U) (r : Reg A) (c : List (Ptr U))
    {g : SM.Rule (Sym U) (Pc U) (Ix U)}
    (h : g q (SM.tops (machine U q r c)) = some (q', fun _ => .skip)) :
    SM.advance g (machine U q r c) = some (machine U q' r c) := by
  unfold SM.advance
  change Option.map _ (g q _) = _
  rw [h]
  rfl

private def update (i : Ix U) (a : SM.Action (Sym U)) :
    Ix U → SM.Action (Sym U) :=
  open Classical in Function.update (fun _ => .skip) i a

omit [Fintype A] in
private theorem next_do (q q' : Pc U) (r r' : Reg A) (c c' : List (Ptr U))
    (i : Ix U) (a : SM.Action (Sym U))
    {g : SM.Rule (Sym U) (Pc U) (Ix U)}
    (h : g q (SM.tops (machine U q r c)) = some (q', update U i a))
    (hx : ∀ l, (update U i a l).perform ((machine U q r c).stack l) =
      (machine U q' r' c').stack l) :
    SM.advance g (machine U q r c) = some (machine U q' r' c') := by
  unfold SM.advance
  change Option.map _ (g q _) = _
  rw [h]
  simp only [Option.map_some, Option.some.injEq]
  change SM.Config.mk q' _ = SM.Config.mk q' _
  congr
  exact funext hx

omit [Fintype A] in
private theorem ret_step (r : Reg A) (p : Ptr U) (c : List (Ptr U)) :
    SM.advance (compile U) (machine U none r (p::c)) = some (machine U (some p) r c) := by
  apply next_do U none (some p) r r (p::c) c none .pop
  · rfl
  · intro l
    cases l <;> simp [machine, update, SM.Action.perform]

def Good (Γ : Scope A) (c : Prog A) : Prop := sites Γ c ⊆ U

def Above (Γ : Scope A) : Prop := ∀ i a, Γ[i]? = some a → Good U (Γ.drop i) a

private theorem pc_good {Γ c} (h : Good U Γ c) :
    pc U Γ c = some ⟨_, h (sites_self c Γ)⟩ := by
  simp [pc, h (sites_self c Γ)]

set_option maxRecDepth 1024 in
theorem Run.compile_ok {Γ c r n s}
    (h : Run Γ c r n s) (hg : Good U Γ c) (ha : Above U Γ) (k : List (Ptr U)) :
    Trace (SM.advance (compile U))
      (machine U (pc U Γ c) r k) n (machine U none s k) := by
  classical
  induction h generalizing k with
  | @pass Γ r =>
    rw [pc_good U hg]
    exact Trace.single (next U _ _ _ _ rfl)
  | @push Γ i a r =>
    have hi := touched_mem U Γ (.push i a) (hg (sites_self _ _))
    change i ∈ used U at hi
    rw [pc_good U hg]
    apply Trace.single
    apply next_do U _ _ r (Function.update r i (a::r i)) k k (some (ix U i)) (.push (.inl a)) (g := compile U)
    · rfl
    · intro l
      cases l with
      | none => simp [machine, update, SM.Action.perform, Function.update_of_ne]
      | some j =>
        by_cases e : j=ix U i
        · subst j
          simp [machine, update, SM.Action.perform, ix_val U _ hi]
        · have e' : j.val ≠ i := fun hz => e (Subtype.ext (hz.trans (ix_val U _ hi).symm))
          simp [machine, update, SM.Action.perform, e, e', Function.update_of_ne]
  | @pop Γ i r =>
    have hi := touched_mem U Γ (.pop i) (hg (sites_self _ _))
    change i ∈ used U at hi
    rw [pc_good U hg]
    apply Trace.single
    apply next_do U _ _ _ _ _ _ (some (ix U i)) .pop (g := compile U)
    · rfl
    · intro l
      cases l with
      | none => simp [machine, update, SM.Action.perform, Function.update_of_ne]
      | some j =>
        by_cases e : j=ix U i
        · subst j
          cases h : r ((ix U i).val) <;>
            simp_all [machine, update, SM.Action.perform, ix_val U _ hi]
        · have e' : j.val ≠ i := fun hz => e (Subtype.ext (hz.trans (ix_val U _ hi).symm))
          simp [machine, update, SM.Action.perform, e, e', Function.update_of_ne]
  | @look Γ i f r n r' h ih =>
    have hh := hg (sites_self _ _)
    have hi := touched_mem U Γ (.look i f) hh
    change i ∈ used U at hi
    have hchild (o : Option A) : Good U Γ (f o) := by
      intro l hl
      apply hg
      rw [sites]
      simp only [List.mem_cons, List.mem_flatMap]
      exact Or.inr ⟨o, mem_options o, hl⟩
    refine Trace.cons (y := machine U (pc U Γ (f (r i).head?)) r k) ?_ (ih (hchild _) ha _)
    rw [pc_good U hg]
    apply next U
    have e := ix_val U i hi
    dsimp [compile, machine, SM.tops]
    cases hlist : r i <;> simp [e, hlist]
  | @join Γ c d r n₁ s n₂ t h₁ h₂ ih jh =>
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
    refine Trace.trans (Trace.trans (Trace.cons (y := machine U (pc U Γ c) r (p::k)) ?_
      (ih hc ha _)) (Trace.single (ret_step U s p k))) ?_
    · rw [pc_good U hg]
      apply next_do U _ _ _ _ k (p::k) none (.push (.inr p)) (g := compile U)
      · dsimp [compile, machine, SM.tops]
        rw [ep]
        rfl
      · intro l
        cases l <;> simp [machine, update, SM.Action.perform, Function.update_of_ne]
    · rw [← ep]
      exact jh hd ha k
  | @tie Γ c r n s h ih =>
    have hc : Good U (c::Γ) c := by
      intro l hl
      apply hg
      rw [sites]
      simp [hl]
    have he : Above U (c::Γ) := by
      intro i a ha'
      cases i with
      | zero =>
        have h : c=a := by simpa using ha'
        subst a
        exact hc
      | succ j =>
        simpa using ha j a (by simpa using ha')
    refine Trace.cons ?_ (ih hc he k)
    rw [pc_good U hg]
    exact next U _ _ _ _ rfl
  | @again Γ i c r n s eq h ih =>
    refine Trace.cons ?_ (ih (ha _ _ eq) ?_ k)
    · rw [pc_good U hg]
      apply next U
      simp [compile, eq]
    · intro j d e
      simp only [List.getElem?_drop] at e
      simpa [List.drop_drop, add_comm] using ha _ _ e


/-- Encapsulate all lists-on-stacks computation as genuine TM computation with alphabet
containing A. Given a successful run from data on stack 0, finish with exactly the
absolute output tape requested (contents of stack 0 at return). Costs linear overhead,
uniform in run despite recursion.
-/
theorem release (p : Prog A) :
    ∃ (X Q I : Type) (_ : Finite X) (_ : Finite Q) (_ : Finite I)
      (sym : A → X) (blank : X) (inp out : I) (_ : inp ≠ out)
      (q : Q) (m : TM.Rule X Q I),
      Function.Injective sym ∧ (∀ a, sym a ≠ blank) ∧
      ∀ (s : List A) (n : ℕ) (r : Reg A), Run [] p (fun i => if i=0 then s else []) n r →
        ∃ finish initTape,
          initTape inp = TM.Tape.loaded blank (s.map sym) ∧
          (∀ i, i ≠ inp → initTape i = TM.Tape.loaded blank []) ∧
          Trace (TM.advance m) ⟨q, initTape⟩ (2*n+1+(r 0).length) finish ∧
          TM.advance m finish = none ∧ TM.whole blank ((r 0).map sym) (finish.tape out) := by
  classical
  let U := sites [] p
  have : Fintype (Ptr U) := Fintype.subtype U.toFinset (by simp)
  have : Fintype (Idx U) := Fintype.subtype (used U).toFinset (by simp)
  refine ⟨Option (Sym U), Option (SM.PC (Sym U) (Pc U) (Ix U)), Option (Ix U), inferInstance, inferInstance, inferInstance,
    fun a => some (.inl a), none, some (some (ix U 0)), none, by simp, some (.inl (pc U [] p)),
    SM.complete (some (ix U 0)) (compile U),
    fun a b e => by simpa using e, by simp, ?_⟩
  intro s n r h
  have hr := Run.compile_ok U h (fun _ e => e) (fun i => by simp) []
  have hi : machine U (pc U [] p) (fun i => if i=0 then s else []) [] =
      SM.origin (pc U [] p) (some (ix U 0)) (s.map Sum.inl) := by
    unfold machine SM.origin
    congr
    funext l
    have hz : (ix U 0).val = 0 := ix_val U _ (by simp [used])
    cases l with
    | none => simp
    | some j =>
      by_cases hj : j=ix U 0
      · subst j
        simp [hz]
      · have e : j.val ≠ 0 := fun hx => hj (Subtype.ext (hx.trans hz.symm))
        simp [e, hj]
  rw [hi] at hr
  obtain ⟨done, ht, hh, hw⟩ := SM.complete_run (k := some (ix U 0)) hr
    (show SM.advance (compile U) (machine U none r []) = none from rfl)
  have hz := ix_val U 0 (by simp [used])
  dsimp [machine] at ht hh hw
  simp only [hz, List.length_map] at ht
  simp only [hz, List.map_map, Function.comp_def] at hw
  refine ⟨done, fun i => if i=some (some (ix U 0)) then TM.Tape.loaded none
      ((s.map Sum.inl).map some) else TM.Tape.loaded none [], ?_, ?_, ht, hh, hw⟩
  · simp [Function.comp_def]
  · intro i e
    simp [e]

end Prog

end IntegerMultiplication
end Computability
end OAI
