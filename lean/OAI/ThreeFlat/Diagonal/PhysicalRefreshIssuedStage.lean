import OAI.ThreeFlat.Diagonal.PhysicalRefreshPreparedStage

namespace OAI
/-! # The issued physical refresh stage and its unique-child certificate -/

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

local notation "inputGraph" => changeLanes A.graph u
local notation "inputWidth" => refreshInput A u port
local notation "outGraph" => RefreshTies.actualPortGraph (RefreshTies.outputGraph inputGraph c sym rows zero hm pad)
local notation "rule" => T.step inputGraph port inputWidth hm hh sym rows zero conn

open private selectedBits outputWords outputShape selectedOutput issuedWords
  from OAI.ThreeFlat.Diagonal.PhysicalRefreshPreparedStage

/-- Transfer the same stage from an explicitly named rewrite to the rewrite of
the selected move, retaining its source words and both presentations of its output. -/
private def reindexStage {K Q : Type} [CommSemiring K] {s : Shape}
    (r r' : Rewrite s K) (eqn : r = r') (i : Fin r.count) (j : Fin r'.count)
    (same : i.val = j.val) (old : Form s Q) {target : Shape} (form : Form target Q)
    (left : r.target i=target) (right : r'.target j=target)
    (stage : Stage r i old (left.symm ▸ form)) : Stage r' j old (right.symm ▸ form) := by
  cases eqn
  cases (Fin.ext same : i = j)
  exact stage

/-- Reindexing keeps the unique child of each original site. The coordinate
on the old shape is obtained from the selected equality of target shapes. -/
private theorem reindexChildren {K Q : Type} [CommSemiring K] {s : Shape}
    (r r' : Rewrite s K) (eqn : r = r') (i : Fin r.count) (j : Fin r'.count)
    (same : i.val = j.val) (old : Form s Q) {target : Shape} (form : Form target Q)
    (left : r.target i = target) (right : r'.target j = target)
    (stage : Stage r i old (left.symm ▸ form)) (parent : (r.target i).Site → s.Site)
    (one : ∀ v, stage.count v = 1) (child : ∀ v k, (stage.child v k).val = parent v)
    (z : (r'.target j).Site) :
    let actual := reindexStage r r' eqn i j same old form left right stage
    actual.count z = 1 ∧ ∀ k, (actual.child z k).val =
      parent (cast (congrArg Shape.Site (right.trans left.symm)) z) := by
  cases eqn
  cases (Fin.ext same : i = j)
  exact ⟨one z, child z⟩

private theorem castSlot {U : Type} (same : U = U) (v : U) : cast same v = v := rfl

private theorem rewriteAgreement : (inIso).rewrite rule = (physMove).rules := rfl

/-- Apply an installer to its selected source while comparing its typed fields separately. -/
private def combine {K P : Type} [CommSemiring K] {s : Shape} {r : Rewrite s K} {i : Fin r.count}
    {input : Form s P} {output : Form (r.target i) P}
    (made : Stage r i input output)
    {s' : Shape} {r' : Rewrite s' K} {j : Fin r'.count} {input' : Form s' P}
    {output' : Form (r'.target j) P} {Y : Sort _}
    (use : Stage r' j input' output' → Y)
    (shapes : s = s') (rules : HEq r r') (indices : i.val = j.val)
    (oldWords : HEq input input') (newWords : HEq output output') : Y := by
  cases shapes
  cases eq_of_heq rules
  cases (Fin.ext indices : i = j)
  cases eq_of_heq oldWords
  cases eq_of_heq newWords
  exact use made

/-- A selected output exists and is exactly the result of the same installer. -/
private theorem existsCombined {K P : Type} [CommSemiring K] {s : Shape} {r : Rewrite s K} {i : Fin r.count}
    {input : Form s P} {output : Form (r.target i) P}
    (made : Stage r i input output)
    {s' : Shape} {r' : Rewrite s' K} {j : Fin r'.count} {input' : Form s' P}
    {output' : Form (r'.target j) P} {Y : Sort _}
    (use : Stage r' j input' output' → Y)
    (shapes : s = s') (rules : HEq r r') (indices : i.val = j.val)
    (oldWords : HEq input input') (newWords : HEq output output') :
    ∃ result : Y, result = combine made use shapes rules indices oldWords newWords :=
  ⟨_, rfl⟩

set_option maxHeartbeats 100000 in
private abbrev acceptSource :=
  existsCombined (RefreshPrepared.sourceStage T A u port hm hh sym rows zero conn L idx)
    (RefreshPrepared.install T A u port hm hh sym rows zero conn L idx)

set_option maxHeartbeats 85000 in
private abbrev atSameRule :=
  acceptSource T A u port hm hh sym rows zero conn L idx rfl
    (heq_of_eq (rewriteAgreement T A u port hm hh sym rows zero conn)) rfl

set_option maxHeartbeats 85000 in
private abbrev atSameInput :=
  atSameRule T A u port hm hh sym rows zero conn L idx HEq.rfl

/-- The final premise of the independently checked installer continuation. -/
private abbrev premiseOf {P : Prop} {Q : P → Prop} (_ : ∀ h : P, Q h) : Prop := P

open private numberedForm from OAI.ThreeFlat.Diagonal.PhysicalRefreshPreparedStage

private theorem readAfterCast (P : Type) (raw destination : Shape) (same : raw = destination)
    (value : Form raw P) : HEq (same ▸ value : Form destination P) value := by
  cases same
  rfl

private theorem wordViews
    (V E U D P : Type) (sites₁ : Fintype V) (edges₁ : Fintype E)
    (sites₂ : Fintype U) (edges₂ : Fintype D)
    (g : PortGraph V E) (g' : PortGraph U D) (w : E → ℕ) (w' : D → ℕ)
    (word : WordLayout g w P) (word' : WordLayout g' w' P)
    (sameSites : V = U) (sameEdges : E = D) (graphs : HEq g g')
    (widths : HEq w w') (issued : HEq word word') :
    HEq (@PortLayout.form (@WordLayout.shape V E sites₁ edges₁ g w) P
      (@WordLayout.ports V E P sites₁ edges₁ g w word)) (numberedForm sites₂ edges₂ word') := by
  cases sameSites
  cases sameEdges
  cases eq_of_heq graphs
  cases eq_of_heq widths
  cases eq_of_heq issued
  cases Subsingleton.elim sites₁ sites₂
  cases Subsingleton.elim edges₁ edges₂
  rfl

set_option maxHeartbeats 110000 in
private theorem installedOutputAgreement :
    premiseOf (atSameInput T A u port hm hh sym rows zero conn L idx) := by
  unfold premiseOf
  -- Use the recorded graph and enumerations of each side. Reconstructing
  -- either enumeration by typeclass search unfolds the finite histogram space.
  run_tac Lean.Elab.Tactic.withMainContext do
    let eqArgs := (← Lean.Elab.Tactic.getMainTarget).getAppArgs
    let a := eqArgs[1]!.getAppArgs
    let b := eqArgs[3]!.getAppArgs
    let raw := a[1]!.getAppArgs
    let state := b[1]!.getAppArgs
    unless raw.size == 6 && state.size == 6 && a.size == 6 && b.size == 6 do
      throwError "expected the two shape transports of the selected word"
    let leftForm := a[3]!.getAppArgs
    let rawWord := leftForm[2]!.appArg!
    let stateWord := b[3]!.appArg!
    let middle := Lean.mkAppN (← Lean.Meta.mkConstWithFreshMVarLevels ``wordViews)
      #[raw[0]!,raw[1]!,state[0]!,state[1]!,leftForm[1]!,
        raw[2]!,raw[3]!,state[2]!,state[3]!,raw[4]!,state[4]!,raw[5]!,state[5]!,
        rawWord,stateWord,
        ← Lean.Meta.mkEqRefl raw[0]!,← Lean.Meta.mkEqRefl raw[1]!,
        ← Lean.Meta.mkHEqRefl raw[4]!,← Lean.Meta.mkHEqRefl raw[5]!,← Lean.Meta.mkHEqRefl rawWord]
    let peel ← Lean.Meta.mkConstWithFreshMVarLevels ``readAfterCast
    let left := Lean.mkAppN peel #[leftForm[1]!,a[1]!,a[4]!,a[5]!,a[3]!]
    let right := Lean.mkAppN peel #[leftForm[1]!,b[1]!,b[4]!,b[5]!,b[3]!]
    let proof ← Lean.Meta.mkHEqTrans left (← Lean.Meta.mkHEqTrans middle (← Lean.Meta.mkHEqSymm right))
    Lean.Elab.Tactic.closeMainGoal `installedOutputAgreement proof

set_option maxHeartbeats 110000 in
private abbrev selectedWitness :=
  atSameInput T A u port hm hh sym rows zero conn L idx
    (installedOutputAgreement T A u port hm hh sym rows zero conn L idx)

set_option maxHeartbeats 110000 in
private abbrev selectedInstalled_eq :=
  Classical.choose_spec (selectedWitness T A u port hm hh sym rows zero conn L idx)

private theorem sourceCount (z : (A.Base × BitWord rem) × Fin m) :
    (RefreshPrepared.sourceStage T A u port hm hh sym rows zero conn L idx).count z = 1 :=
  refreshInputStage_count T A u port hm hh sym rows zero conn L idx (selectedBits T A u port hm hh sym rows zero conn idx)
    (outputWords (Pins:=Pins) T A u port hm hh sym rows zero conn idx)
    (outputShape T A u port hm hh sym rows zero conn idx)
    (selectedOutput T A u port hm hh sym rows zero conn L idx)
    (issuedWords T A u port hm hh sym rows zero conn L idx) z

private theorem sourceChild (z : (A.Base × BitWord rem) × Fin m)
    (k : Fin ((RefreshPrepared.sourceStage T A u port hm hh sym rows zero conn L idx).count z)) :
    ((RefreshPrepared.sourceStage T A u port hm hh sym rows zero conn L idx).child z k).val =
      (inIso).site.symm z :=
  refreshInputStage_child T A u port hm hh sym rows zero conn L idx (selectedBits T A u port hm hh sym rows zero conn idx)
    (outputWords (Pins:=Pins) T A u port hm hh sym rows zero conn idx)
    (outputShape T A u port hm hh sym rows zero conn idx)
    (selectedOutput T A u port hm hh sym rows zero conn L idx)
    (issuedWords T A u port hm hh sym rows zero conn L idx) z k

private abbrev uniqueChild {K P : Type} [CommSemiring K] {s : Shape} {r : Rewrite s K}
    {i : Fin r.count} {input : Form s P} {output : Form (r.target i) P}
    (stage : Stage r i input output) (parent : (r.target i).Site → s.Site) : Prop :=
  ∀ v, stage.count v = 1 ∧ ∀ k, (stage.child v k).val = parent v

private theorem combineChildren {K P : Type} [CommSemiring K] {s : Shape} {r : Rewrite s K}
    {i : Fin r.count} {input : Form s P} {output : Form (r.target i) P} (made : Stage r i input output)
    {s' : Shape} {r' : Rewrite s' K} {j : Fin r'.count} {input' : Form s' P}
    {output' : Form (r'.target j) P} {Y : Sort _} (use : Stage r' j input' output' → Y)
    (shapes : s = s') (rules : HEq r r') (indices : i.val = j.val)
    (oldWords : HEq input input') (newWords : HEq output output')
    (property : Y → Prop) (oldParent : (r.target i).Site → s.Site) (newParent : (r'.target j).Site → s'.Site)
    (parents : HEq oldParent newParent) (single : uniqueChild made oldParent)
    (keep : ∀ stage, uniqueChild stage newParent → property (use stage)) :
    property (combine made use shapes rules indices oldWords newWords) := by
  cases shapes
  cases eq_of_heq rules
  cases (Fin.ext indices : i = j)
  cases eq_of_heq oldWords
  cases eq_of_heq newWords
  cases eq_of_heq parents
  exact keep made single

set_option maxHeartbeats 100000 in
private abbrev childrenSource :=
  combineChildren (RefreshPrepared.sourceStage T A u port hm hh sym rows zero conn L idx)
    (RefreshPrepared.install T A u port hm hh sym rows zero conn L idx)

set_option maxHeartbeats 85000 in
private abbrev childrenRule :=
  childrenSource T A u port hm hh sym rows zero conn L idx rfl
    (heq_of_eq (rewriteAgreement T A u port hm hh sym rows zero conn)) rfl

set_option maxHeartbeats 85000 in
private abbrev childrenInput :=
  childrenRule T A u port hm hh sym rows zero conn L idx HEq.rfl

set_option maxHeartbeats 85000 in
private abbrev childrenOutput :=
  childrenInput T A u port hm hh sym rows zero conn L idx
    (installedOutputAgreement T A u port hm hh sym rows zero conn L idx)

set_option maxHeartbeats 85000 in
private abbrev childrenChart :=
  childrenOutput T A u port hm hh sym rows zero conn L idx
    (fun actual => uniqueChild actual (inIso).site.symm) (inIso).site.symm (inIso).site.symm HEq.rfl

set_option maxHeartbeats 100000 in
private abbrev physicalChildren :=
  childrenChart T A u port hm hh sym rows zero conn L idx
    (fun z => ⟨sourceCount T A u port hm hh sym rows zero conn L idx z,
      sourceChild T A u port hm hh sym rows zero conn L idx z⟩)
    (fun _ single z => ⟨(single z).1, (single z).2⟩)


end
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
