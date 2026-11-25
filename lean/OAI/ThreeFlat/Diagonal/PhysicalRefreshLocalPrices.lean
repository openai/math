import OAI.ThreeFlat.Diagonal.PhysicalRefreshWordPrice
import OAI.ThreeFlat.Diagonal.HistorySelectedChronology
import OAI.ThreeFlat.Diagonal.PhysicalLocalTariff
import OAI.ThreeFlat.Diagonal.PhysicalTreeResources
import OAI.ThreeFlat.Diagonal.PhysicalRunCharges
import OAI.ThreeFlat.Diagonal.PhysicalBlockSchedule
import OAI.ThreeFlat.Diagonal.PhysicalRefreshAssembly
import OAI.ThreeFlat.Diagonal.HistoryPhysicalStages

namespace OAI
/-! # Finite tile prices and the typed resources of a selected refresh -/

namespace ThreeFlat.Diagonal.PhysicalStage
open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression CompressorPacking HistoryContraction
open scoped Classical BigOperators
open private sum_congr_instances from OAI.ThreeFlat.Diagonal.RefreshKernel
noncomputable section

private theorem height_from_word_room {repeats bits u : ℕ}
    (count : repeats≤2^(u^10)) (digit : bits≤2^(u^10)) :
    HistogramTileNetwork.siteHeight repeats bits≤16*u^10 := by
  apply Nat.clog_le_of_le_pow
  apply le_trans _ (Nat.pow_le_pow_right (by decide : 0<2) (show u^10+u^10≤16*u^10 by omega))
  rw [pow_add]
  exact max_le (count.trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))) (Nat.mul_le_mul count digit)

private theorem copies_le_charge {width copies previous total : ℕ} (charged : 1+width+copies+previous≤total) :
    copies≤total := by omega

private theorem oneChild_width {U S : Type} [Fintype U] (owner : U→S) (v : S) {n : ℕ}
    (ord : Fin n ≃ {x : U // owner x=v}) (source : U) (count : n=1)
    (child : ∀ i,(ord i).val=source) (w : U→ℕ) (population : Fintype {x : U // owner x=v}) :
    w source=Finset.sum (@Finset.univ _ population) (fun a => w a.val) := by
  let : Fintype {x : U // owner x=v} := population
  calc
    _ = ∑ _ : Fin n,w source := by simp [count]
    _ = ∑ i : Fin n,w (ord i).val :=
      Finset.sum_congr rfl (fun i _ => congrArg w (child i).symm)
    _ = _ := ord.sum_comp (fun a=>w a.val)

private theorem push_from_population {F : Type} [Field F] {d l D m : ℕ} {A : State d l}
    (R : Move F A D m) (b : Fin R.rules.count) (next : (R.next b).Site → ℕ)
    (previous : A.Site → ℕ) (v : (R.next b).Site)
    (population : Fintype {x : A.Site // R.parent b x=v}) :
    next v+Finset.sum (@Finset.univ _ population) (fun x => previous x.val) = R.push b next previous v := by
  unfold Move.push
  exact congrArg (next v+·) (sum_congr_instances (fun x : {x : A.Site // R.parent b x=v} => rfl))

namespace Block
variable {F Pins : Type} [Field F] [Fintype F] (B : Block F) {rem : ℕ}
/-- A physical refresh has exactly one preimage under its input chart. -/
private theorem chart_width {U V : Type} [Fintype U] (chart : U ≃ V) (owner : U → V)
    (agrees : ∀ x, owner x = chart x) (v : V) (width : U → ℕ) :
    width (chart.symm v) = ∑ x : {x // owner x = v}, width x.val := by
  classical
  let center : {x // owner x = v} := ⟨chart.symm v, (agrees _).trans (chart.apply_symm_apply v)⟩
  have unique (x : {x // owner x = v}) : x = center := by
    apply Subtype.ext
    exact chart.injective ((agrees x.val).symm.trans (x.property.trans (chart.apply_symm_apply v).symm))
  let order : Fin 1 ≃ {x // owner x = v} :=
    ⟨fun _ => center, fun _ => 0, fun _ => Subsingleton.elim _ _, fun x => (unique x).symm⟩
  exact oneChild_width owner v order (chart.symm v) rfl (fun _ => rfl) width inferInstance

omit [Fintype F] in
/-- Charge the actual elected chart cost to its physical predecessor and successor widths. -/
private theorem chart_fresh_paid {d l D n : ℕ} {X : State d l} (R : Move F X D n)
    (L : X.Words Pins) (b : Fin R.rules.count) (chart : X.Site ≃ (R.next b).Site)
    (owner : ∀ u, R.parent b u = chart u) (fresh : (R.next b).Words Pins)
    (q : (R.next b).Site → ℕ) (prev : X.Site → ℕ) (v : (R.next b).Site) (copies W actual : ℕ)
    (previous : ∀ x, 1 + X.incidentWidth x ≤ prev x)
    (localCharge : 1 + (R.next b).incidentWidth v + copies ≤ q v)
    (raw : actual ≤ (2+B.refreshPrice)*(W+1)^3*
      (1+(L.ports.halfBits (chart.symm v)+fresh.ports.halfBits v)+copies)) :
    actual ≤ (B.localCoefficient*(W+1)^3)*R.push b q prev v := by
  classical
  have prior := (X.words_incidentWidth L (chart.symm v)).trans
    (chart_width chart (R.parent b) owner v X.incidentWidth)
  rw [prior, (R.next b).words_incidentWidth fresh v] at raw
  have priced := B.local_cost_to_push (fun x : {x // R.parent b x = v} => prev x.val)
    (fun x => X.incidentWidth x.val) (q v) copies ((R.next b).incidentWidth v)
    actual (2+B.refreshPrice) W W (fun x => (Nat.le_add_left _ 1).trans (previous x.val))
    localCharge le_rfl B.refresh_local_coefficient raw
  exact priced.trans_eq (congrArg (fun total => (B.localCoefficient*(W+1)^3)*total)
    (push_from_population R b q prev v inferInstance))

/-- The actual fresh resource count and its pushed site charge after a degree recast. -/
private abbrev recastPrice {d l D D' n K : ℕ} {X : State d l} (R : Move F X D n)
    (degree : D = D') (J : R.Assembler Pins) (L : X.Words Pins)
    (b : Fin (Program.recastMove degree R).rules.count) (q : Program.siteCharge R K)
    (prev : X.Site → ℕ) (v : ((Program.recastMove degree R).next b).Site) (coefficient : ℕ) : Prop :=
  let move := Program.recastMove degree R
  let step := Move.outputAssembler degree R J L b
  step.stage.freshResources (Move.WordStep.targetSite (R := move) (i := b) v) ≤
    coefficient * move.push b ((Program.siteRecast degree R q).val b) prev v

private abbrev basePrice {d l D n K : ℕ} {X : State d l} (R : Move F X D n)
    (J : R.Assembler Pins) (L : X.Words Pins) (b : Fin R.rules.count)
    (q : Program.siteCharge R K) (prev : X.Site → ℕ) (v : (R.next b).Site) (coefficient : ℕ) : Prop :=
  (J L b).stage.freshResources (Move.WordStep.targetSite (R := R) (i := b) v) ≤
    coefficient * R.push b (q.val b) prev v

omit [Fintype F] in
private theorem price_at_degree {d l D D' n K : ℕ} {X : State d l} (R : Move F X D n)
    (degree : D = D') (J : R.Assembler Pins) (L : X.Words Pins) (b : Fin R.rules.count)
    (q : Program.siteCharge R K) (prev : X.Site → ℕ) (coefficient : ℕ)
    (pay : ∀ v, basePrice R J L b q prev v coefficient)
    (v : ((Program.recastMove degree R).next (Program.degreeTerm degree R b)).Site) :
    recastPrice R degree J L (Program.degreeTerm degree R b) q prev v coefficient := by
  cases degree
  exact pay v

omit [Fintype F] in
private theorem price_if_degree {d l D D' n K : ℕ} {X : State d l} (R : Move F X D n)
    (degree : D = D') (J : R.Assembler Pins) (L : X.Words Pins) (q : Program.siteCharge R K)
    (prev : X.Site → ℕ) (coefficient limit : ℕ)
    (pay : ∀ b v, R.push b (q.val b) prev v ≤ limit → basePrice R J L b q prev v coefficient)
    (b : Fin (Program.recastMove degree R).rules.count) (v : ((Program.recastMove degree R).next b).Site)
    (peak : (Program.recastMove degree R).push b ((Program.siteRecast degree R q).val b) prev v ≤ limit) :
    recastPrice R degree J L b q prev v coefficient := by
  cases degree
  exact pay b v peak

open private assembleWords WordRead WordOrder refreshWordRead refreshWordOriginOrder
  from OAI.ThreeFlat.Diagonal.PhysicalRefreshWords

omit [Fintype F] in
private theorem assembled_fresh {d l D n : ℕ} {X : State d l} (move : Move F X D n)
    (i : Fin move.rules.count) (source : X.Words Pins) (target : (move.next i).Words Pins)
    (stage : StageFor move i source target) (halves : (move.next i).OrderedHalves target)
    (origin : OriginFor move i source target) (read : WordRead move i source target origin)
    (order : WordOrder move i source target stage origin) (z : (move.rules.target i).Site)
    (issued : move.WordStep Pins source i)
    (same : issued = assembleWords move i source target stage halves origin read order) :
    issued.stage.freshResources z = stage.freshResources z := by
  cases same
  rfl

section
attribute [local irreducible] Stage.freshResources refreshWordStage
variable {m l hb r h p : ℕ} {c : Fin m → Fin m → ℕ} {C gap : ℝ}
  (T : RefreshMotif.Table F c (1+h+p) C) (X : State m l)
  (u : BitWord l ≃+ BitWord hb × BitWord r) (tag : Fin m ≃ BitWord hb)
  (hm : 2 ≤ m) (hh : 0 < h) (sym : ∀ i j, c i j = c j i)
  (row : ∀ i, ∑ j, c i j = h) (zero : ∀ i, c i i = 0) (conn : Expander.Bound (Expander.transition c h) ℝ gap)
local notation "issued" => refreshMove T X u tag hm hh sym row zero conn

set_option maxRecDepth 3200 in
set_option maxHeartbeats 180000 in
private abbrev move_fresh_eq (L : X.Words Pins) (i : Fin (issued).rules.count)
    (z : (X.Base × BitWord r) × Fin m) :=
  assembled_fresh (F := F) (Pins := Pins) (X := X) (issued) i L
    (refreshWords T X u tag hm hh sym row zero conn L i)
    (refreshWordStage T X u tag hm hh sym row zero conn L i)
    (refreshWords_ordered T X u tag hm hh sym row zero conn L i)
    (refreshOrigin T X u tag hm hh sym row zero conn L i)
    (refreshWordRead T X u tag hm hh sym row zero conn L i)
    (refreshWordOriginOrder T X u tag hm hh sym row zero conn L i) z
end

omit [Fintype F] in
private theorem charge_on_same_move {d l D n : ℕ} {X : State d l} (R R' : Move F X D n)
    (same : R = R') (L : X.Words Pins) (i : Fin R.rules.count) (j : Fin R'.rules.count)
    (index : i.val = j.val) (z : (R.rules.target i).Site) (z' : (R'.rules.target j).Site)
    (site : HEq z z') (a : R.WordStep Pins L i) (a' : R'.WordStep Pins L j) (step : HEq a a') :
    a.stage.freshResources z = a'.stage.freshResources z' := by
  subst R'
  have ij : i = j := Fin.ext index
  subst j
  cases eq_of_heq site
  cases eq_of_heq step
  rfl

set_option maxRecDepth 3200 in
set_option maxHeartbeats 140000 in
/-- The rule-level binary assembler retains the tree produced by the selected refresh stage. -/
private abbrev binary_source_eq {s t h pad : ℕ} {c : Fin (2^s) → Fin (2^s) → ℕ} {C gap : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) (X : State (2^s) (s+t))
    (hm : 2 ≤ 2^s) (hh : 0 < h) (sym : ∀ i j, c i j = c j i)
    (row : ∀ i, ∑ j, c i j = h) (zero : ∀ i, c i i = 0) (conn : Expander.Bound (Expander.transition c h) ℝ gap)
    (L : X.Words Pins) (b : Fin (refreshBinary T X hm hh sym row zero conn).rules.count)
    (z : (X.Base × BitWord t) × Fin (2^s)) :=
  move_fresh_eq T X (splitWord s t) (Native.tagOrdinal s).symm hm hh sym row zero conn L b z
    (refreshMove_assembler (Pins := Pins) T X (splitWord s t) (Native.tagOrdinal s).symm hm hh sym row zero conn L b) rfl

set_option maxRecDepth 3200 in
set_option maxHeartbeats 180000 in
private abbrev binary_projection_eq {s t h pad : ℕ} {c : Fin (2^s) → Fin (2^s) → ℕ} {C gap : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) (X : State (2^s) (s+t))
    (hm : 2 ≤ 2^s) (hh : 0 < h) (sym : ∀ i j, c i j = c j i)
    (row : ∀ i, ∑ j, c i j = h) (zero : ∀ i, c i i = 0) (conn : Expander.Bound (Expander.transition c h) ℝ gap)
    (L : X.Words Pins) (b : Fin (refreshBinary T X hm hh sym row zero conn).rules.count)
    (z : (X.Base × BitWord t) × Fin (2^s)) :=
  charge_on_same_move (F := F) (Pins := Pins)
    (refreshBinary T X hm hh sym row zero conn)
    (refreshMove T X (splitWord s t) (Native.tagOrdinal s).symm hm hh sym row zero conn) rfl
    L b b rfl z z HEq.rfl (refreshBinary_assembler T X hm hh sym row zero conn L b)
    (refreshMove_assembler T X (splitWord s t) (Native.tagOrdinal s).symm hm hh sym row zero conn L b)
    HEq.rfl

set_option maxRecDepth 3200 in
set_option maxHeartbeats 180000 in
private abbrev binary_fresh_eq {s t h pad : ℕ} {c : Fin (2^s) → Fin (2^s) → ℕ} {C gap : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) (X : State (2^s) (s+t))
    (hm : 2 ≤ 2^s) (hh : 0 < h) (sym : ∀ i j, c i j = c j i)
    (row : ∀ i, ∑ j, c i j = h) (zero : ∀ i, c i i = 0) (conn : Expander.Bound (Expander.transition c h) ℝ gap)
    (L : X.Words Pins) (b : Fin (refreshBinary T X hm hh sym row zero conn).rules.count)
    (z : (X.Base × BitWord t) × Fin (2^s)) :=
  (binary_projection_eq T X hm hh sym row zero conn L b z).trans
    (binary_source_eq T X hm hh sym row zero conn L b z)

local notation "s₀" => B.exponent B.levels
variable (A : State (2^(B.exponent B.levels)) (B.exponent B.levels+rem))
local notation "split₁" => splitWord s₀ rem
set_option quotPrecheck false in
local notation "tag₁" => (Native.tagOrdinal s₀).symm
local notation "G₁" => changeLanes A.graph split₁
local notation "w₁" => refreshInput A split₁ tag₁
local notation "I₁" => StageAddress.refreshInputIso A.graph A.chart split₁ tag₁ A.width
local notation "T₁" => B.refresh
local notation "M₁" => refreshBinary T₁ A B.hm B.hh B.symmetric B.degree B.loopless B.connected
local notation "J₁" => refreshBinary_assembler (Pins := Pins) T₁ A B.hm B.hh B.symmetric B.degree B.loopless B.connected
local notation "q₁" => refreshBinaryCharge T₁ A B.hm B.hh B.symmetric B.degree B.loopless B.connected
set_option quotPrecheck false in
local notation "n₁" => (T₁).repeats G₁ tag₁ w₁
set_option quotPrecheck false in
local notation "tiles₁" => (T₁).entry G₁ tag₁ w₁
set_option quotPrecheck false in
local notation "rs₁" => (T₁).step G₁ tag₁ w₁ B.hm B.hh B.symmetric B.degree B.loopless B.connected

omit [Fintype F] in
private theorem base_at_site {d l D n K : ℕ} {X : State d l} (R : Move F X D n)
    (J : R.Assembler Pins) (L : X.Words Pins) (b : Fin R.rules.count)
    (q : Program.siteCharge R K) (prev : X.Site → ℕ) (v : (R.next b).Site)
    (numbered : (R.rules.target b).Site) (coefficient : ℕ)
    (siteEq : Move.WordStep.targetSite (R:=R) (i:=b) v = numbered)
    (charge : (J L b).stage.freshResources numbered ≤ coefficient * R.push b (q.val b) prev v) :
    basePrice R J L b q prev v coefficient :=
  (congrArg (J L b).stage.freshResources siteEq).le.trans charge

private theorem numbered_site_self {U : Type} (eqn : U = U) (v : U) :
    (Equiv.cast eqn).symm v=v := rfl

section PublicRefresh
open Expander MotifOuterTerms

private def fixedRefreshRows (B : Block F) (V : ℕ) : StaticMotif F→Prop
  | .shrink .. => True
  | .refresh s _ _ c _ T => ∀ i : Fin (T.last+1),(T.block i).bitCap≤V ∧
      ∀ j : Fin (2^s),1+Tree.portTariff (RefreshMotif.denseGraph _) (RefreshTies.ports c)
        (T.base i) (T.block i).bits (Fintype.card (T.block i).Alphabet) (T.block i).bitCap j≤B.refreshPrice

omit [Fintype F] in
private theorem prices_of_recognized (B : Block F) {V : ℕ} {motif : StaticMotif F}
    (recognized : motif = .refresh (B.exponent B.levels) B.h B.pad B.graph _ B.refresh)
    (cap : ∀ i : Fin (B.refresh.last+1), (B.refresh.block i).bitCap ≤ V) :
    fixedRefreshRows B V motif := by
  rw [recognized]
  exact fun i => ⟨cap i, B.refresh_tile_price i⟩

variable {s t a p : ℕ} {c : Fin (2^s)→Fin (2^s)→ℕ} {C γ : ℝ}
    (T : RefreshMotif.Table F c (1+a+p) C)
    (hm : 2≤2^s) (hh : 0<a) (sym : ∀ i j,c i j=c j i) (row : ∀ i,∑ j,c i j=a)
    (zero : ∀ i,c i i=0) (conn : Bound (transition c a) ℝ γ)
    (X : State (2^s) (s+t))
set_option quotPrecheck false in
local notation "ports₂" => (Native.tagOrdinal s).symm
local notation "G₂" => changeLanes X.graph (splitWord s t)
local notation "w₂" => refreshInput X (splitWord s t) ports₂
local notation "I₂" => StageAddress.refreshInputIso X.graph X.chart (splitWord s t) ports₂ X.width
local notation "M₂" => refreshBinary T X hm hh sym row zero conn
local notation "J₂" => refreshBinary_assembler (Pins := Pins) T X hm hh sym row zero conn
local notation "q₂" => refreshBinaryCharge T X hm hh sym row zero conn
local notation "n₂" => T.repeats G₂ ports₂ w₂
local notation "tile₂" => T.entry G₂ ports₂ w₂
local notation "rs₂" => T.step G₂ ports₂ w₂ hm hh sym row zero conn

set_option maxRecDepth 3500 in
omit [Fintype F] in
private theorem publicTileRoom (b : Fin (M₂).rules.count) (u : ℕ) (prev : X.Site → ℕ)
    (v : (X.Base × BitWord t) × Fin (2^s))
    (cap : (tile₂ v.1).bitCap ≤ 2^(u^10))
    (peak : (M₂).push b (q₂ b) prev v ≤ 2^(u^10)) :
    HistogramTileNetwork.siteHeight (n₂ v.1) (tile₂ v.1).bitCap ≤ 16*u^10 := by
  change 1+((M₂).next b).incidentWidth v+n₂ v.1+_≤2^(u^10) at peak
  exact height_from_word_room (copies_le_charge peak) cap

open private outputWords from OAI.ThreeFlat.Diagonal.PhysicalRefreshPreparedStage

set_option maxRecDepth 4800 in
set_option maxHeartbeats 500000 in
omit [Fintype F] in
private theorem publicSelectedPrice (L : X.Words Pins) (b : Fin (M₂).rules.count) (W : ℕ)
    (v : (X.Base × BitWord t) × Fin (2^s))
    (fee : RefreshTies.refreshTariff c (fun g => T.base (T.winner G₂ ports₂ w₂ g))
      (T.entry G₂ ports₂ w₂) v.1 v.2 ≤ B.refreshPrice)
    (height : HistogramTileNetwork.siteHeight (n₂ v.1) (tile₂ v.1).bitCap ≤ W) :
    (refreshWordStage T X (splitWord s t) ports₂ hm hh sym row zero conn L b).freshResources v ≤ (2+B.refreshPrice)*(W+1)^3*
      (1+(L.ports.halfBits ((I₂).site.symm v)+(((M₂).next b).halfWords Pins).ports.halfBits v)+n₂ v.1) := by
  have paid := refreshWordStage_price T X (splitWord s t) ports₂ hm hh sym row zero conn L b v
    B.refreshPrice W fee height
  unfold outputWords at paid
  unfold refreshBinary
  exact paid

set_option maxRecDepth 4800 in
set_option maxHeartbeats 500000 in
omit [Fintype F] in
private theorem publicRawWordPrice (L : X.Words Pins) (b : Fin (M₂).rules.count) (W : ℕ)
    (v : (X.Base × BitWord t) × Fin (2^s))
    (fee : RefreshTies.refreshTariff c (fun g => T.base (T.winner G₂ ports₂ w₂ g))
      (T.entry G₂ ports₂ w₂) v.1 v.2 ≤ B.refreshPrice)
    (height : HistogramTileNetwork.siteHeight (n₂ v.1) (tile₂ v.1).bitCap ≤ W) :
    (J₂ L b).stage.freshResources v ≤ (2+B.refreshPrice)*(W+1)^3*
      (1+(L.ports.halfBits ((I₂).site.symm v)+(((M₂).next b).halfWords Pins).ports.halfBits v)+n₂ v.1) := by
  have stored := binary_fresh_eq T X hm hh sym row zero conn L b v
  have paid := publicSelectedPrice (Pins := Pins) B T hm hh sym row zero conn X L b W v fee height
  exact stored.le.trans paid

set_option maxRecDepth 3500 in
set_option maxHeartbeats 300000 in
omit [Fintype F] in
private theorem publicNativeCharge (L : X.Words Pins) (b : Fin (M₂).rules.count) (u : ℕ)
    (prev : X.Site → ℕ) (previous : ∀ x, 1+X.incidentWidth x ≤ prev x)
    (v : (X.Base × BitWord t) × Fin (2^s))
    (frozen : fixedRefreshRows B (2^(u^10)) (.refresh s a p c C T))
    (peak : (M₂).push b (q₂ b) prev v ≤ 2^(u^10)) :
    (J₂ L b).stage.freshResources v ≤ (B.localCoefficient*(16*u^10+1)^3)*(M₂).push b (q₂ b) prev v := by
  have bounds := frozen (T.winner G₂ ports₂ w₂ v.1)
  have height := publicTileRoom T hm hh sym row zero conn X b u prev v bounds.1 peak
  have raw := publicRawWordPrice B T hm hh sym row zero conn X L b (16*u^10) v (bounds.2 v.2) height
  exact chart_fresh_paid (Pins := Pins) B M₂ L b (I₂).site
    (refreshParent T X (splitWord s t) ports₂ hm hh sym row zero conn b)
    (((M₂).next b).halfWords Pins) (q₂ b) prev v (n₂ v.1) (16*u^10)
    ((J₂ L b).stage.freshResources v) previous le_rfl raw

set_option maxRecDepth 8192 in
set_option maxHeartbeats 220000 in
omit [Fintype F] in
private theorem publicRefreshAt {K : ℕ}
    (recognized : StaticMotif.refresh s a p c C T=.refresh (B.exponent B.levels) B.h B.pad B.graph _ B.refresh)
    (fund : ∀ b,(∑ v,q₂ b v)≤K*(X.positions+X.widthSum+((M₂).next b).positions+((M₂).next b).widthSum))
    (L : X.Words Pins) (b : Fin (M₂).rules.count) (u : ℕ) (prev : X.Site→ℕ)
    (previous : ∀ x,1+X.incidentWidth x≤prev x)
    (cap : ∀ i : Fin (B.refresh.last+1),(B.refresh.block i).bitCap≤2^(u^10))
    (v : (X.Base × BitWord t) × Fin (2^s)) (peak : (M₂).push b (q₂ b) prev v ≤ 2^(u^10)) :
    basePrice (Pins := Pins) M₂ (refreshBinary_assembler (Pins := Pins) T X hm hh sym row zero conn) L b
      (⟨q₂,fund⟩ : Program.siteCharge M₂ K) prev v (B.localCoefficient*(16*u^10+1)^3) := by
  refine base_at_site (Pins := Pins) M₂ J₂ L b (⟨q₂,fund⟩ : Program.siteCharge M₂ K)
    prev v v (B.localCoefficient*(16*u^10+1)^3)
    (@numbered_site_self ((X.Base × BitWord t) × Fin (2^s))
      (congrArg Shape.Site ((M₂).target_eq b)) v) ?_
  exact publicNativeCharge B T hm hh sym row zero conn X L b u prev previous v
    (prices_of_recognized B recognized cap) peak

set_option maxRecDepth 8192 in
set_option maxHeartbeats 220000 in
omit [Fintype F] in
/-- Fixed-family recognition transports only the actual scalar tile price and digit
width. The chronological tree, owner fiber and charge all remain those of the issued move. -/
theorem public_refresh_fresh {D K : ℕ}
    (recognized : StaticMotif.refresh s a p c C T=.refresh (B.exponent B.levels) B.h B.pad B.graph _ B.refresh)
    (deg : 1+a+p=D)
    (fund : ∀ b,(∑ v,q₂ b v)≤K*(X.positions+X.widthSum+((M₂).next b).positions+((M₂).next b).widthSum))
    (L : X.Words Pins) (b : Fin (Program.recastMove deg M₂).rules.count) (u : ℕ) (prev : X.Site→ℕ)
    (previous : ∀ x,1+X.incidentWidth x≤prev x)
    (cap : ∀ i : Fin (B.refresh.last+1),(B.refresh.block i).bitCap≤2^(u^10))
    (v : ((Program.recastMove deg M₂).next b).Site)
    (peak : let R:=Program.recastMove deg M₂
            R.push b ((Program.siteRecast deg M₂ (⟨q₂,fund⟩ : Program.siteCharge M₂ K)).val b) prev v≤2^(u^10)) :
    recastPrice (Pins := Pins) M₂ deg (refreshBinary_assembler (Pins := Pins) T X hm hh sym row zero conn) L b (⟨q₂,fund⟩ : Program.siteCharge M₂ K) prev v
      (B.localCoefficient*(16*u^10+1)^3) := by
  exact price_if_degree (Pins := Pins) M₂ deg (refreshBinary_assembler (Pins := Pins) T X hm hh sym row zero conn) L
    (⟨q₂,fund⟩ : Program.siteCharge M₂ K) prev (B.localCoefficient*(16*u^10+1)^3) (2^(u^10))
    (fun branch site paid => publicRefreshAt (Pins := Pins) (B := B) (T := T) (X := X)
      (hm := hm) (hh := hh) (sym := sym) (row := row) (zero := zero) (conn := conn)
      recognized fund L branch u prev previous cap site paid) b v peak

end PublicRefresh

section FixedChartPrice
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
attribute [local irreducible] Stage.freshResources refreshWordStage

omit [Fintype F] in
private theorem fixed_numbered_site (b : Fin (M₁).rules.count)
    (v : (A.Base × BitWord rem) × Fin (2^s₀)) :
    Move.WordStep.targetSite (R:=M₁) (i:=b) v = v :=
  @numbered_site_self ((A.Base × BitWord rem) × Fin (2^s₀))
    (congrArg Shape.Site ((M₁).target_eq b)) v

omit [Fintype F] in
private theorem fixed_elected_price (L : A.Words Pins) (b : Fin (M₁).rules.count)
    (W : ℕ) (v : (A.Base × BitWord rem) × Fin (2^s₀))
    (height : HistogramTileNetwork.siteHeight (n₁ v.1) (tiles₁ v.1).bitCap ≤ W) :
    (J₁ L b).stage.freshResources v ≤ (2+B.refreshPrice)*(W+1)^3*
      (1+(L.ports.halfBits ((I₁).site.symm v)+(((M₁).next b).halfWords Pins).ports.halfBits v)+n₁ v.1) :=
  publicRawWordPrice (Pins := Pins) B B.refresh B.hm B.hh B.symmetric B.degree B.loopless
    B.connected A L b W v (B.refresh_tile_price (B.refresh.winner G₁ tag₁ w₁ v.1) v.2) height

omit [Fintype F] in
private theorem fixed_parent_price (L : A.Words Pins) (b : Fin (M₁).rules.count)
    (W : ℕ) (prev : A.Site → ℕ) (previous : ∀ x,1+A.incidentWidth x≤prev x)
    (v : (A.Base × BitWord rem) × Fin (2^s₀))
    (height : HistogramTileNetwork.siteHeight (n₁ v.1) (tiles₁ v.1).bitCap ≤ W) :
    (J₁ L b).stage.freshResources v ≤ (B.localCoefficient*(W+1)^3)*(M₁).push b (q₁ b) prev v :=
  chart_fresh_paid B M₁ L b (I₁).site
    (refreshParent B.refresh A split₁ tag₁ B.hm B.hh B.symmetric B.degree B.loopless B.connected b)
    (((M₁).next b).halfWords Pins) (q₁ b) prev v (n₁ v.1) W ((J₁ L b).stage.freshResources v)
    previous le_rfl (fixed_elected_price B A L b W v height)

omit [Fintype F] in
private theorem fixed_chart_pay {K : ℕ}
    (fund : ∀ t,(∑ v,q₁ t v)≤K*(A.positions+A.widthSum+((M₁).next t).positions+((M₁).next t).widthSum))
    (L : A.Words Pins) (b : Fin (M₁).rules.count) (W : ℕ) (prev : A.Site → ℕ)
    (previous : ∀ x,1+A.incidentWidth x≤prev x)
    (heights : ∀ g : A.Base×BitWord rem,HistogramTileNetwork.siteHeight (n₁ g) (tiles₁ g).bitCap≤W)
    (v : (A.Base × BitWord rem) × Fin (2^s₀)) :
    basePrice M₁ J₁ L b (⟨q₁,fund⟩ : Program.siteCharge M₁ K) prev v (B.localCoefficient*(W+1)^3) :=
  base_at_site M₁ J₁ L b (⟨q₁,fund⟩ : Program.siteCharge M₁ K) prev v v
    (B.localCoefficient*(W+1)^3) (fixed_numbered_site B A b v)
    (fixed_parent_price B A L b W prev previous v (heights v.1))

end FixedChartPrice

set_option maxRecDepth 8192 in
set_option maxHeartbeats 220000 in
omit [Fintype F] in
/-- The canonical refresh's own integer charge pays its typed fresh resources
before the native history stream is allocated. -/
theorem refresh_fresh_to_push {D K : ℕ} (deg : 1+B.h+B.pad=D)
    (fund : ∀ t,(∑ v,q₁ t v)≤K*(A.positions+A.widthSum+((M₁).next t).positions+((M₁).next t).widthSum))
    (L : A.Words Pins) (b : Fin (M₁).rules.count) (W : ℕ) (prev : A.Site→ℕ)
    (previous : ∀ x,1+A.incidentWidth x≤prev x)
    (heights : ∀ g : A.Base×BitWord rem,HistogramTileNetwork.siteHeight (n₁ g) (tiles₁ g).bitCap≤W)
    (v : ((Program.recastMove deg M₁).next (Program.degreeTerm deg M₁ b)).Site) :
    recastPrice (Pins := Pins) M₁ deg J₁ L (Program.degreeTerm deg M₁ b)
      (⟨q₁,fund⟩ : Program.siteCharge M₁ K) prev v (B.localCoefficient*(W+1)^3) := by
  exact price_at_degree M₁ deg J₁ L b (⟨q₁,fund⟩ : Program.siteCharge M₁ K)
    prev (B.localCoefficient*(W+1)^3) (fixed_chart_pay B A fund L b W prev previous heights) v

set_option maxRecDepth 8192 in
omit [Fintype F] in
/-- Each elected group's copy count occurs at every true successor port, so one
such port supplies its sorter-height bound directly from the propagated charge. -/
theorem refresh_heights_from_push {D K : ℕ} (deg : 1+B.h+B.pad=D)
    (fund : ∀ t,(∑ v,q₁ t v)≤K*(A.positions+A.widthSum+((M₁).next t).positions+((M₁).next t).widthSum))
    (b : Fin (M₁).rules.count) (u : ℕ) (prev : A.Site→ℕ)
    (cap : ∀ i : Fin (B.refresh.last+1),(B.refresh.block i).bitCap≤2^(u^10))
    (peak : let R:=Program.recastMove deg M₁
            let t:=Program.degreeTerm deg M₁ b
            ∀ v,R.push t ((Program.siteRecast deg M₁ (⟨q₁,fund⟩ : Program.siteCharge M₁ K)).val t) prev v≤2^(u^10)) :
    ∀ g : A.Base×BitWord rem,HistogramTileNetwork.siteHeight (n₁ g) (tiles₁ g).bitCap≤16*u^10 := by
  cases deg
  intro g
  let z : ((M₁).next b).Site:=(g,⟨0,Nat.two_pow_pos _⟩)
  have localRoom:=peak z
  change 1+((M₁).next b).incidentWidth z+n₁ g+_≤2^(u^10) at localRoom
  have count : n₁ g≤2^(u^10) := copies_le_charge localRoom
  have digit : (tiles₁ g).bitCap≤2^(u^10):=cap ((T₁).winner G₁ tag₁ w₁ g)
  exact height_from_word_room count digit



end Block
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
