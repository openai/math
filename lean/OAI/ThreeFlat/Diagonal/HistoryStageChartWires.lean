import OAI.ThreeFlat.Diagonal.PhysicalRefreshWordStage
import OAI.ThreeFlat.Diagonal.HistoryStageRefreshSourceWires

namespace OAI
/-! # Physical chart changes preserve the numerical addresses in an ordered join -/

namespace ThreeFlat.Diagonal.PhysicalStage

open LinearAlgebra.SpectralBooks Expander Computability.VPVNP.Compression CompressorPacking HistoryContraction
open RAM.HistoryStageShapeWires
open scoped Classical BigOperators
noncomputable section

variable {F Pins : Type} [Field F]

open private combine rewriteAgreement installedOutputAgreement
  from OAI.ThreeFlat.Diagonal.PhysicalRefreshIssuedStage
open private selectedStage_heq
  from OAI.ThreeFlat.Diagonal.PhysicalRefreshWordStage

private theorem combined_wires {S : Shape} (L : PortLayout S Pins) {r r' : Rewrite S F}
    {i : Fin r.count} {j : Fin r'.count} {out : Form (r.target i) Pins}
    {before after : Form (r'.target j) Pins}
    (made : Stage r i L.form out) (install : Stage r' j L.form before → Stage r' j L.form after)
    (rules : r=r') (indices : i.val=j.val) (outputs : HEq out before)
    (sites : (r'.target j).Site=(r.target i).Site) (v : (r'.target j).Site) (external : ℕ)
    (source : At L made (cast sites v) external)
    (keep : ∀ stage,At L stage v external → At L (install stage) v external) :
    At L (combine made install rfl (heq_of_eq rules) indices HEq.rfl outputs) v external := by
  cases rules
  cases (Fin.ext indices : i=j)
  cases eq_of_heq outputs
  exact keep made source

open private assembleWords WordRead WordOrder refreshWordRead refreshWordOriginOrder
  from OAI.ThreeFlat.Diagonal.PhysicalRefreshWords

private theorem assembled_wires {d l D n : ℕ} {X : State d l} (move : Move F X D n)
    (i : Fin move.rules.count) (source : X.Words Pins) (target : (move.next i).Words Pins)
    (stage : StageFor move i source target) (halves : (move.next i).OrderedHalves target)
    (origin : OriginFor move i source target) (read : WordRead move i source target origin)
    (order : WordOrder move i source target stage origin) (z : (move.rules.target i).Site)
    (v : (move.next i).Site) (step : move.WordStep Pins source i)
    (same : step = assembleWords move i source target stage halves origin read order)
    (wires : At source.ports stage z (target.ext v)) :
    At source.ports step.stage z (step.words.ext v) := by
  cases same
  exact wires

private def assemblerWires {d l D n : ℕ} {X : State d l} (move : Move F X D n)
    (assembler : move.Assembler Pins) : Prop :=
  ∀ (layout : X.Words Pins) (i : Fin move.rules.count) (v : (move.next i).Site),
    let step := assembler layout i
    At layout.ports step.stage (Move.WordStep.targetSite (R:=move) (i:=i) v) (step.words.ext v)

private theorem cast_site_heq {U V : Type} (e : U=V) (v : V) : HEq ((Equiv.cast e).symm v) v := by
  cases e
  rfl

private theorem assemblerWires_of_sites {d l D n : ℕ} {X : State d l} (move : Move F X D n)
    (assembler : move.Assembler Pins)
    (place : ∀ i, (move.next i).Site → (move.rules.target i).Site)
    (same : ∀ i v, HEq (place i v) v)
    (read : ∀ (layout : X.Words Pins) i v,
      At layout.ports (assembler layout i).stage (place i v) ((assembler layout i).words.ext v)) :
    assemblerWires move assembler := by
  intro layout i v
  have target : HEq (Move.WordStep.targetSite (R:=move) (i:=i) v) v :=
    cast_site_heq (congrArg Shape.Site (move.target_eq i)) v
  have located := eq_of_heq ((same i v).trans target.symm)
  exact (congrArg (fun z => At layout.ports (assembler layout i).stage z
    ((assembler layout i).words.ext v)) located).mp (read layout i v)

section Issued
variable {m lanes hbits rem h pad : ℕ} {c : Fin m→Fin m→ℕ} {K γ : ℝ}
  (T : RefreshMotif.Table F c (1+h+pad) K) (A : State m lanes)
  (u : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)
  (hm : 2 ≤ m) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
  (zero : ∀ i,c i i=0) (conn : Bound (transition c h) ℝ γ)
  (L : A.Words Pins) (idx : Fin (refreshMove T A u port hm hh sym rows zero conn).rules.count)

set_option quotPrecheck false
attribute [local irreducible] CompressorRefresh.graph RefreshTies.freshWidth
  RefreshMotif.Table.wordStageOnChart RefreshTies.refreshAssemblyAtWidth

local notation "outW" => refreshWords T A u port hm hh sym rows zero conn L idx
local notation "srcS" => RefreshPrepared.sourceStage T A u port hm hh sym rows zero conn L idx
local notation "issue" => RefreshPrepared.install T A u port hm hh sym rows zero conn L idx

set_option maxHeartbeats 220000 in
private abbrev wiresAt :=
  combined_wires L.ports srcS issue (rewriteAgreement T A u port hm hh sym rows zero conn) rfl

set_option maxHeartbeats 220000 in
private abbrev wiresForm :=
  wiresAt T A u port hm hh sym rows zero conn L idx
    (installedOutputAgreement T A u port hm hh sym rows zero conn L idx) rfl

private def preservesNumberedWires {K P : Type} [Field K] {S : Shape}
    {r : Rewrite S K} {i : Fin r.count} (l : PortLayout S P)
    {before after : Form (r.target i) P}
    (install : Stage r i l.form before → Stage r i l.form after) : Prop :=
  ∀ (z : (r.target i).Site) (external : ℕ) (stage : Stage r i l.form before),
    At l stage z external → At l (install stage) z external

open private installNumbered numberedForm_eq selectedBits selectedOutput outputShape sameGraph sameBits sameIssuedOutput
  from OAI.ThreeFlat.Diagonal.PhysicalRefreshPreparedStage

private theorem numbered_wires {K P : Type} [Field K] {d l D n : ℕ} {source : State d l}
    (r : Move K source D n) (i : Fin r.rules.count) (input : source.Words P) (output : (r.next i).Words P)
    (sites : Fintype (r.next i).Site) (edges : Fintype (((r.next i).Base × Fin D) × BitWord n))
    (graph : PortGraph (r.next i).Site (((r.next i).Base × Fin D) × BitWord n))
    (bits : ((r.next i).Base × Fin D) × BitWord n → ℕ) (word : WordLayout graph bits P)
    (shape : r.rules.target i = @WordLayout.shape _ _ sites edges graph bits)
    (graphEq : graph = (r.next i).shape.graph) (bitsEq : bits = (r.next i).width)
    (wordEq : HEq word output) :
    preservesNumberedWires input.ports
      (installNumbered r i input output sites edges graph bits word shape graphEq bitsEq wordEq) := by
  intro z external stage read
  exact read.reform (numberedForm_eq sites (r.next i).finiteSite edges (r.next i).shape.edgeFintype
    graphEq bitsEq word output wordEq shape (r.target_eq i))

set_option maxHeartbeats 110000 in
private abbrev chartNumberedAt :=
  numbered_wires (refreshMove T A u port hm hh sym rows zero conn) idx L outW

set_option maxHeartbeats 110000 in
private abbrev chartLayoutAt :=
  chartNumberedAt T A u port hm hh sym rows zero conn L idx
    (inferInstance : Fintype ((A.Base × BitWord rem) × Fin m))
    (inferInstance : Fintype (RefreshTies.LiveSlot A.Base (BitWord rem) m (1+h+pad)))
    (RefreshTies.actualPortGraph (RefreshTies.outputGraph (changeLanes A.graph u) c sym rows zero hm pad))

set_option maxHeartbeats 110000 in
private abbrev chartWordsAt :=
  chartLayoutAt T A u port hm hh sym rows zero conn L idx
    (selectedBits T A u port hm hh sym rows zero conn idx)
    (selectedOutput T A u port hm hh sym rows zero conn L idx)
    (outputShape T A u port hm hh sym rows zero conn idx)

set_option maxHeartbeats 110000 in
private abbrev installWires :=
  chartWordsAt T A u port hm hh sym rows zero conn L idx
    (sameGraph T A u port hm hh sym rows zero conn idx)
    (sameBits T A u port hm hh sym rows zero conn idx)
    (sameIssuedOutput T A u port hm hh sym rows zero conn L idx)

set_option maxHeartbeats 250000 in
private abbrev wiresInstalled (v : (A.Base × BitWord rem) × Fin m) :=
  wiresForm T A u port hm hh sym rows zero conn L idx v ((outW).ext v)
    (RefreshPrepared.source_wires T A u port hm hh sym rows zero conn L idx v)
    (installWires T A u port hm hh sym rows zero conn L idx v ((outW).ext v))

attribute [local irreducible] combine RefreshIssued.selected RefreshPrepared.sourceStage
  RefreshPrepared.install refreshWords

set_option maxHeartbeats 240000 in
private theorem installed_stage_wires (v : (A.Base × BitWord rem) × Fin m) :
    At L.ports (refreshWordStage T A u port hm hh sym rows zero conn L idx) v ((outW).ext v) := by
  let observe (stage : StageFor (refreshMove T A u port hm hh sym rows zero conn) idx L outW) :=
    At L.ports stage v ((outW).ext v)
  have casted := eq_of_heq (selectedStage_heq T A u port hm hh sym rows zero conn L idx)
  have same := casted.trans (RefreshIssued.selected_eq T A u port hm hh sym rows zero conn L idx)
  exact (congrArg observe same).mpr (wiresInstalled T A u port hm hh sym rows zero conn L idx v)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 650000 in
private theorem move_stage_wires (v : (A.Base × BitWord rem) × Fin m) :
    let step := refreshMove_assembler T A u port hm hh sym rows zero conn L idx
    At L.ports step.stage v (step.words.ext v) :=
  assembled_wires (F:=F) (Pins:=Pins) (X:=A) (refreshMove T A u port hm hh sym rows zero conn) idx L
    (refreshWords T A u port hm hh sym rows zero conn L idx)
    (refreshWordStage T A u port hm hh sym rows zero conn L idx)
    (refreshWords_ordered T A u port hm hh sym rows zero conn L idx)
    (refreshOrigin T A u port hm hh sym rows zero conn L idx)
    (refreshWordRead T A u port hm hh sym rows zero conn L idx)
    (refreshWordOriginOrder T A u port hm hh sym rows zero conn L idx)
    v v (refreshMove_assembler T A u port hm hh sym rows zero conn L idx) rfl
    (installed_stage_wires T A u port hm hh sym rows zero conn L idx v)

attribute [local irreducible] refreshMove_assembler

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem refresh_assembler_wires :
    assemblerWires (refreshMove T A u port hm hh sym rows zero conn)
      (refreshMove_assembler (Pins:=Pins) T A u port hm hh sym rows zero conn) :=
  assemblerWires_of_sites (refreshMove T A u port hm hh sym rows zero conn)
    (refreshMove_assembler (Pins:=Pins) T A u port hm hh sym rows zero conn)
    (fun _ v => v) (fun _ _ => HEq.rfl)
    (move_stage_wires T A u port hm hh sym rows zero conn)

end Issued

private theorem wires_degree_term {d l D D' m : ℕ} {A : State d l}
    (R : Move F A D m) (J : R.Assembler Pins) (L : A.Words Pins) (i : Fin R.rules.count)
    (e : D=D') (wire : assemblerWires R J)
    (v : ((Program.recastMove e R).next (Program.degreeTerm e R i)).Site) :
    let b := Program.degreeTerm e R i
    let s := Move.outputAssembler e R J L b
    At L.ports s.stage (Move.WordStep.targetSite (R:=Program.recastMove e R) (i:=b) v) (s.words.ext v) := by
  cases e
  exact wire L i v

section Binary
attribute [local irreducible] refreshWordStage refreshWords refreshMove_assembler
variable {s rem h pad D : ℕ} {c : Fin (2^s)→Fin (2^s)→ℕ} {K γ : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) K) (A : State (2^s) (s+rem))
    (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
    (noLoop : ∀ i,c i i=0) (conn : Bound (transition c h) ℝ γ)
    (L : A.Words Pins) (branch : Fin (refreshBinary T A hm hh sym rows noLoop conn).rules.count)
set_option quotPrecheck false
local notation "M₁" => refreshBinary T A hm hh sym rows noLoop conn
local notation "J₁" => refreshBinary_assembler T A hm hh sym rows noLoop conn

set_option maxRecDepth 8192 in
set_option maxHeartbeats 650000 in
private theorem binary_uncast_wires :
    assemblerWires M₁ (refreshBinary_assembler (Pins:=Pins) T A hm hh sym rows noLoop conn) :=
  refresh_assembler_wires (m:=2^s) (lanes:=s+rem) (hbits:=s) (rem:=rem)
    (Pins:=Pins) T A (splitWord s rem) (Native.tagOrdinal s).symm hm hh sym rows noLoop conn

variable (deg : 1+h+pad=D)
local notation "M₂" => Program.recastMove deg M₁
local notation "branch₂" => Program.degreeTerm deg M₁ branch
local notation "ws" => Move.outputAssembler deg M₁ J₁ L branch₂

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- All three numerical wire observations at the selected native refresh,
including the physical old chart and the compiled successor-degree transport. -/
theorem refreshBinary_assembler_wires (v : ((M₂).next branch₂).Site) :
    At L.ports (ws).stage (Move.WordStep.targetSite (R:=M₂) (i:=branch₂) v) ((ws).words.ext v) :=
  wires_degree_term M₁ J₁ L branch deg
    (binary_uncast_wires T A hm hh sym rows noLoop conn) v

end Binary
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
