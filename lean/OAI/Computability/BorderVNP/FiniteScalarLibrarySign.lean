import OAI.Computability.BorderVNP.FiniteScalarLibraryCalls
import OAI.Computability.BorderVNP.DiagonalNativeSiteMacro

/-! # Exact signed path of the finite-field scalar opcode

The word-RAM still asks its private routine for a signed outcome. On the
canonically packed count interval the field-returning opcode has one accepting
empty choice string, positive in that signed control, even if its actual scalar
output is zero. Every nonempty choice tape is rejected.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteScalarLibrary

open TeamPrivateTape TeamSite VPVNP.BurstRAM

variable {F : Type*} [Field F] [Fintype F] {Q : Type} {m w d : ℕ}

/-- A deterministic bit-track table with a positive sign at every accepting halt. -/
private def Positive {S : Type} {k : ℕ} (P : Table S k) := ∀ q heads,
  match P q heads with
  | .halt _ sign => sign = false
  | .one _ => True
  | .two .. => False

private def positiveSymbol {S Γ : Type} {k : ℕ} : TapeChoice S Γ k → Prop
  | .halt _ b => b=false
  | .one _ => True
  | .two .. => False

private theorem round_rows (q : FiniteScalarRounds.Phase (Fintype.card F)) (h : Fin 1 → Option Bool) :
    positiveSymbol (FiniteScalarRounds.table F q h) := by
  cases q <;> cases val : h 0 <;> first
    | (simp only [FiniteScalarRounds.table,val,positiveSymbol]; trivial)
    | (rename_i b; cases b <;> simp only [FiniteScalarRounds.table,val,positiveSymbol] <;> trivial)

private theorem scalar_rows (tape : Fin m) :
    let M := scalarMacro (Q := Q) F tape
    Positive (trackTable M.alphabet M.table) := by
  intro M q heads
  have rule (v : Control Q F) (sym : Fin m → Option Bool) : positiveSymbol (M.table v sym) := by
    cases v with
    | inl _ => rfl
    | inr z =>
      change positiveSymbol (rightTable _ (FiniteScalarRounds.table F) (.inr z) sym)
      have hs := round_rows z (fun _ => sym tape)
      cases h : FiniteScalarRounds.table F z (fun _ => sym tape) <;> simp only [rightTable,h,positiveSymbol] at hs ⊢; exact hs
  let sym := fun i => M.alphabet.read (fun j => heads (finProdFinEquiv (i,j)))
  have hs := rule q sym
  unfold trackTable
  cases h : M.table q sym <;> simp only [sym,h,positiveSymbol] at hs ⊢; exact hs

private theorem nonempty_rejected {S : Type} {k : ℕ} (P : Table S k) (pos : Positive P)
    (f : ℕ) (q : S) (t : Fin k → Track) (b : Bool) (bs : List Bool) :
    TeamPrivateCall.evaluate P f q t (b::bs) = none := by
  induction f generalizing q t with
  | zero => rfl
  | succ f ih =>
    have pp := pos q (heads t)
    cases h : P q (heads t) with
    | halt ok sg => simp [TeamPrivateCall.evaluate,h]
    | one c => simpa only [TeamPrivateCall.evaluate,h] using ih c.next (c.apply t)
    | two l r => simp [h] at pp

omit [Field F] [Fintype F] in
private theorem positive_halt {S : Type} {k : ℕ} (P : Table S k) (pos : Positive P)
    (weight : S → (Fin k → Bool) → Bool → F) (fuel : ℕ) (q : S) (ts : Fin k → Track) (v : F)
    (accept : FieldProcessor.trackReturn P weight fuel q ts [] = some v) :
    ∃ u, TeamPrivateCall.evaluate P fuel q ts [] = some (some false,u) := by
  induction fuel generalizing q ts with
  | zero => simp [FieldProcessor.trackReturn] at accept
  | succ fuel ih =>
    have pp := pos q (heads ts)
    cases h : P q (heads ts) with
    | halt ok sg =>
      have sign : sg=false := by simpa only [h] using pp
      cases ok with
      | false => simp [FieldProcessor.trackReturn,h] at accept
      | true => exact ⟨ts,by simp [TeamPrivateCall.evaluate,h,sign]⟩
    | one c => simpa only [TeamPrivateCall.evaluate,h] using ih c.next (c.apply ts) (by simpa only [FieldProcessor.trackReturn,h] using accept)
    | two l r => simp [h] at pp

/-- Exact signed acceptance of the fetched scalar routine on the authentic
word-RAM interval. Surplus bits cannot create a second accepted path. -/
theorem scalar_eval (F : Type*) [Field F] [Fintype F]
    (lib : Fin 8 → Macro Q (Option Bool) m AlphabetWidth) (c : FiniteScalarRounds.Index F → Fin d → Bool)
    (hw : 0<w) (fuel : ℕ) (budget : 2*d*Fintype.card F < fuel) (bs : List Bool) :
    (combine F lib 1).eval fuel (RoutingISA.CompactFrame.pack w (FiniteScalarRounds.stream F c)) bs =
      if bs.isEmpty then some .plus else none := by
  let M := scalarMacro (Q := Q) F (lib 1).inputTape
  let T := trackTable M.alphabet M.table
  let vs := RoutingISA.CompactFrame.pack w (FiniteScalarRounds.stream F c)
  have hp : Positive T := scalar_rows _
  rw [combine,ite_eq_left rfl]
  change (TeamPrivateCall.evaluate T fuel M.start (M.initial vs) bs).map _ = _
  cases bs with
  | cons b bs => rw [nonempty_rejected T hp]; rfl
  | nil =>
    let ew := rightReturn (Q := Q) (lib 1).inputTape (FiniteScalarRounds.result F)
    let E : TeamRAM.Event w := ⟨.burst 0 vs.length,vs,[],.plus⟩
    have hr := scalar_return F lib (fun _ _ _ _ => 1) c hw E fuel rfl budget
    change FieldSelect.nativeReturn M.table M.alphabet.blank ew fuel M.start
      (input M.alphabet.blank M.digit M.inputTape (TeamPrivateCall.inputBits vs)) [] = some _ at hr
    have ht := (FieldProcessor.trackReturn_eq M ew fuel M.start
      (input M.alphabet.blank M.digit M.inputTape (TeamPrivateCall.inputBits vs)) []).trans hr
    obtain ⟨u,h⟩ := positive_halt T hp _ fuel M.start (M.initial vs) _ ht
    rw [h]
    rfl

/-- The actual library passed to the finite team instruction at slot one. -/
theorem macro_one (F : Type*) [Field F] [Fintype F]
    (lib : Fin 8 → Macro Q (Option Bool) m AlphabetWidth) (c : FiniteScalarRounds.Index F → Fin d → Bool)
    (hw : 0<w) (fuel : ℕ) (budget : 2*d*Fintype.card F < fuel) (bs : List Bool) :
    TeamSiteEvents.macros (combine F lib) fuel 1 (RoutingISA.CompactFrame.pack w (FiniteScalarRounds.stream F c)) bs =
      if bs.isEmpty then some .plus else none :=
  scalar_eval F lib c hw fuel budget bs

end FiniteScalarLibrary

end BorderVNP
end Computability
end OAI
