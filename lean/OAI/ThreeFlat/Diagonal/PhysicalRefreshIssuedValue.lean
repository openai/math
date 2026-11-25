import OAI.ThreeFlat.Diagonal.PhysicalRefreshIssuedStage

namespace OAI
/-! # The selected data of the issued physical refresh stage -/

namespace ThreeFlat.Diagonal.PhysicalStage
open LinearAlgebra.SpectralBooks Expander Computability.VPVNP.Compression CompressorPacking HistoryContraction
open scoped Classical BigOperators
noncomputable section

variable {F Pins : Type} [Field F] {m lanes hbits rem h pad : ℕ} {c : Fin m→Fin m→ℕ} {C γ : ℝ}
  (T : RefreshMotif.Table F c (1+h+pad) C) (A : State m lanes)
  (u : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)
  (hm : 2 ≤ m) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
  (zero : ∀ i,c i i=0) (conn : Bound (transition c h) ℝ γ)

set_option quotPrecheck false

local notation "physMove" => refreshMove T A u port hm hh sym rows zero conn
local notation "inIso" => StageAddress.refreshInputIso A.graph A.chart u port A.width

attribute [local irreducible] CompressorRefresh.graph RefreshTies.freshWidth
  RefreshMotif.Table.wordStageOnChart RefreshTies.refreshAssemblyAtWidth

section
variable (L : A.Words Pins) (idx : Fin (refreshMove T A u port hm hh sym rows zero conn).rules.count)

open private selectedWitness selectedInstalled_eq combine rewriteAgreement installedOutputAgreement from OAI.ThreeFlat.Diagonal.PhysicalRefreshIssuedStage

namespace RefreshIssued

open Lean Elab Term in
local elab "issuedTypeOf% " w:term:max : term => do
  let witness ← elabTerm w none
  let carrier ← Meta.whnf (← Meta.inferType witness)
  unless carrier.isAppOfArity ``Exists 2 do throwError "expected the selected stage witness"
  return ← instantiateMVars carrier.getAppArgs[0]!

open Lean Elab Term in
local elab "installedResult% " w:term:max : term => do
  let certified ← elabTerm w none
  let equation ← Meta.whnf (← Meta.inferType certified)
  unless equation.isAppOfArity ``Eq 3 do throwError "expected the certified installer equation"
  return equation.getAppArgs[2]!

/-- The stage type in the original finite-choice installer's output. -/
def stageType := issuedTypeOf% (selectedWitness T A u port hm hh sym rows zero conn L idx)

/-- A result is issued exactly when the registered installer accepts the original source. -/
private def realizes {S X Y : Sort _} (source : S) (install : X → Y) (result : Y) : Prop :=
  ∃ x : X, HEq x source ∧ result = install x

private theorem uniqueRealization {S X Y : Sort _} {source : S} {install : X → Y} {r z : Y}
    (first : realizes source install r) (second : realizes source install z) : r = z := by
  obtain ⟨x,hx,rfl⟩ := first
  obtain ⟨y,hy,rfl⟩ := second
  exact congrArg install (eq_of_heq (hx.trans hy.symm))

private theorem existsRealized {K P : Type} [CommSemiring K] {s : Shape} {r : Rewrite s K} {i : Fin r.count}
    {input : Form s P} {output : Form (r.target i) P}
    (made : Stage r i input output)
    {s' : Shape} {r' : Rewrite s' K} {j : Fin r'.count} {input' : Form s' P}
    {output' : Form (r'.target j) P} {Y : Sort _}
    (use : Stage r' j input' output' → Y)
    (shapes : s = s') (rules : HEq r r') (indices : i.val = j.val)
    (oldWords : HEq input input') (newWords : HEq output output') :
    ∃ result : Y, realizes made use result ∧ result = combine made use shapes rules indices oldWords newWords := by
  cases shapes
  cases eq_of_heq rules
  cases (Fin.ext indices : i = j)
  cases eq_of_heq oldWords
  cases eq_of_heq newWords
  exact ⟨use made, ⟨made, HEq.rfl, rfl⟩, rfl⟩

private abbrev realizesSource :=
  existsRealized (RefreshPrepared.sourceStage T A u port hm hh sym rows zero conn L idx)
    (RefreshPrepared.install T A u port hm hh sym rows zero conn L idx)

private abbrev realizesInput :=
  realizesSource T A u port hm hh sym rows zero conn L idx rfl
    (heq_of_eq (rewriteAgreement T A u port hm hh sym rows zero conn)) rfl HEq.rfl

private abbrev realization :=
  realizesInput T A u port hm hh sym rows zero conn L idx
    (installedOutputAgreement T A u port hm hh sym rows zero conn L idx)

open Lean Elab Term in
local elab "installerInputType% " x:term:max : term => do
  let f ← elabTerm x none
  let .forallE _ input _ _ ← Meta.whnf (← Meta.inferType f) | throwError "expected the stage installer"
  return ← instantiateMVars input

/-- The output of the genuine installer, with its input identified with the
independently verified source stage. -/
private inductive NativeResult :
    (issuedTypeOf% (selectedWitness T A u port hm hh sym rows zero conn L idx)) → Prop where
  | installed (x : (installerInputType% (RefreshPrepared.install T A u port hm hh sym rows zero conn L idx)))
      (original : HEq x (RefreshPrepared.sourceStage T A u port hm hh sym rows zero conn L idx)) :
      NativeResult (RefreshPrepared.install T A u port hm hh sym rows zero conn L idx x)

private theorem hasResult :
    ∃ result : (issuedTypeOf% (selectedWitness T A u port hm hh sym rows zero conn L idx)),
      NativeResult T A u port hm hh sym rows zero conn L idx result := by
  obtain ⟨r,⟨x,same,eligible⟩,_⟩ := realization T A u port hm hh sym rows zero conn L idx
  refine Exists.intro r ?_
  rw [eligible]
  exact NativeResult.installed (T := T) (A := A) (u := u) (port := port)
    (hm := hm) (hh := hh) (sym := sym) (rows := rows) (zero := zero)
    (conn := conn) (L := L) (idx := idx) x same

set_option genSizeOf false in
/-- A certified output uses the precise receiver type from the native witness.
The box lets choice operate on a single datatype with a known projection. -/
private structure IssuedOutput where
  value : (issuedTypeOf% (selectedWitness T A u port hm hh sym rows zero conn L idx))
  original : NativeResult T A u port hm hh sym rows zero conn L idx value

private theorem outputExists :
    Nonempty (IssuedOutput T A u port hm hh sym rows zero conn L idx) := by
  obtain ⟨r, real⟩ := hasResult T A u port hm hh sym rows zero conn L idx
  exact ⟨⟨r, real⟩⟩

private def outputBox : IssuedOutput T A u port hm hh sym rows zero conn L idx :=
  Classical.choice (outputExists T A u port hm hh sym rows zero conn L idx)

/-- The value contained in the certified original installer output. -/
def selected :=
  (outputBox T A u port hm hh sym rows zero conn L idx).value

private theorem everyResult
    (z : issuedTypeOf% (selectedWitness T A u port hm hh sym rows zero conn L idx))
    (actual : NativeResult T A u port hm hh sym rows zero conn L idx z) :
    z = installedResult% (selectedInstalled_eq T A u port hm hh sym rows zero conn L idx) := by
  obtain ⟨w, real, expected⟩ := realization T A u port hm hh sym rows zero conn L idx
  cases actual with
  | installed x same =>
    refine Eq.trans ?_ expected
    exact uniqueRealization ⟨x,same,rfl⟩ real

abbrev selected_eq :=
  everyResult T A u port hm hh sym rows zero conn L idx
    (selected T A u port hm hh sym rows zero conn L idx)
    (outputBox T A u port hm hh sym rows zero conn L idx).original


end RefreshIssued
end
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
