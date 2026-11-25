import OAI.Hierarchy.DescentOrdinaryNodeOrder
import OAI.Hierarchy.DescentStageEdgeReceipt

namespace OAI
/-! # The single measured scan shared by physical cable and scalar-node ordinals -/

namespace Hierarchy.DescentStageEdgeReceipt

open DescentSixParty DescentSixParty.StarKeys DescentHostDirectory DescentKernelHistory
open scoped Classical BigOperators
noncomputable section

variable {F P H : Type} [Field F] [Fintype H] [DecidableEq H]
variable {d : ℕ} {bits : P→ℕ} {u ε : ℝ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable (he : 0≤ε) (T : StageInput W G u ε) (choice : (T.result he).Choice)
variable (oldID : W.graph.Edge ↪ Fin (Fintype.card W.graph.Edge)) (rootRank : H ↪ ℕ)
set_option quotPrecheck false
local notation "scan" => BitDescription.scannedRows he T
local notation "home" => BitDescription.scanHome T (scan).μ
local notation "color" => BitDescription.scanColor T (scan).μ (scan).α (scan).β
local notation "constantZ" => fun _ : (scan).pairs=>T.z

private abbrev RangeType {A B : Type} (_ : A→B) := B
abbrev ScanColonies := RangeType (home)
abbrev scanHomeAt := (home)
abbrev scanColorAt := (color)
abbrev ScanNumbers := (scan).pairs ≃ Fin (Fintype.card (scan).pairs)

open DescentColonies DescentGL DescentWalshTables DescentHostDegree
local notation "sourceMass" => W.siteUnits T.hub T.records T.wire 256 T.hist
local notation "indices" => BitDescription.scanBlocks T (scan).μ
local notation "capacity" => (T.wire*(T.z*G.b)*T.cap)
local notation "smallCells" => small_reindexed W.graph T.pos T.block sourceMass T.small (multiplier T.fieldBits (scan).μ)

def nativeAddress : ScanColonies he T ↪ T.V×(ℕ×ℕ) :=
  occupiedAddress W.graph capacity T.near (gap T.Δ) (packExponent 20 T.Δ)
    (blockMass W.graph T.pos indices sourceMass) smallCells T.pos indices

theorem scanHomeAt_surjective : Function.Surjective (scanHomeAt he T) :=
  colonyOf_surjective W.graph capacity T.near (gap T.Δ) (packExponent 20 T.Δ)
    (blockMass W.graph T.pos indices sourceMass) smallCells T.pos indices

theorem nativeAddress_legal (c : ScanColonies he T) :
    thickKey (nativeAddress he T c)∈keys T.k 1 := by
  obtain ⟨v,rfl⟩ := colonyOf_surjective W.graph capacity T.near (gap T.Δ) (packExponent 20 T.Δ)
    (blockMass W.graph T.pos indices sourceMass) smallCells T.pos indices c
  have address := occupiedAddress_colonyOf W.graph capacity T.near (gap T.Δ) (packExponent 20 T.Δ)
    (blockMass W.graph T.pos indices sourceMass) smallCells T.pos indices v
  apply (congrArg (fun c : T.V×(ℕ×ℕ) => thickKey c ∈ keys T.k 1) address).mpr
  have shallow := depth_le (blockMass W.graph T.pos indices sourceMass) (fun p q => q ∈ T.near p)
    (gap T.Δ) (packExponent 20 T.Δ) capacity smallCells (T.pos v) (indices v)
  exact key_mem (T.pos v) (indices v) (shallow.trans (Nat.sub_le ..)) (by decide : 0<1)

private abbrev scanOrdinals : ScanNumbers he T :=
  DescentPacking.PairRAM.globalNumberBy W.graph W.core (home) (color) T.cap
    (DescentPacking.originalId (ScanColonies he T))

/-- The native first-site order of occupied colonies and the accepted units in each
whole pack fix the matched row before its profile is chosen. -/
def nativeNumbers (_rank : T.V↪ℕ) : ScanNumbers he T := scanOrdinals he T

private abbrev scanKey (col : ScanColonies he T ↪ H×(ℕ×ℕ))
    (same : ∀e∈W.core,scanColorAt he T (W.graph.src e)=scanColorAt he T (W.graph.dst e)) :=
  nativeKey W.graph W.core (scanHomeAt he T) (scanColorAt he T) T.cap col same
    (bestLayout (branchWidth G (fun _ : (scan).pairs => T.z) ((scan).profile choice)))

/-- Both the cable tape and the pair ordinals are indices of one constructor.
Its paint and multiplier come directly from the chosen measured scan. -/
inductive IssuedRows (he : 0≤ε) (T : StageInput W G u ε) (choice : (T.result he).Choice)
    (oldID : W.graph.Edge ↪ Fin (Fintype.card W.graph.Edge)) (rootRank : H ↪ ℕ) : (S : MarkedWorld F d P bits)→(n : Normalize S)→
    Tape n.result.graph.Edge→ScanNumbers he T→Prop where
  | stage (col : ScanColonies he T ↪ H×(ℕ×ℕ))
      (same : ∀e∈W.core,scanColorAt he T (W.graph.src e)=scanColorAt he T (W.graph.dst e))
      (hub : H→Bool) (k g q : ℕ) (legal : ∀c,thickKey (col c)∈keys k 1)
      (source : (∃rank : T.V↪ℕ, HEq rank rootRank ∧
        DescentPacking.PairRAM.globalNumberBy W.graph W.core (scanHomeAt he T) (scanColorAt he T) T.cap
          (DescentPacking.originalId (ScanColonies he T))=nativeNumbers he T rank) ∧
        k=T.k ∧ g=gainExponent 20 T.Δ ∧
        (∀v,nativeKey W.graph W.core (scanHomeAt he T) (scanColorAt he T) T.cap col same
          (bestLayout (branchWidth G (fun _=>T.z) ((BitDescription.scannedRows he T).profile choice))) v∈
          keys T.k (2^(packExponent 20 T.Δ)+2)) ∧ HEq col (nativeAddress he T) ∧
        (∀ci,(col ci).2=(nativeAddress he T ci).2) ∧
        ∀u,HEq (col (scanHomeAt he T u)).1 (T.pos u) ∧ hub (col (scanHomeAt he T u)).1=T.hub u)
      (old : ∀e∈W.core,q∣W.graph.width e) (used : ∀j,(BitDescription.scannedRows he T).pick j∈W.core)
      (cut : ∀_i : (BitDescription.scannedRows he T).pairs,q∣T.z) :
      IssuedRows he T choice oldID rootRank _
        (MarkedWorld.subroundNormalize (I := (BitDescription.scannedRows he T).pairs) W G
          (BitDescription.scannedRows he T).pick (fun _=>T.z) (fun _=>T.unitPos)
          (BitDescription.scannedRows he T).fit (BitDescription.scannedRows he T).pack
          ((BitDescription.scannedRows he T).profile choice) (scanKey he T choice col same)
          hub k g q old used cut)
        (ordinary W G oldID (scanOrdinals he T) (BitDescription.scannedRows he T).pick
          (fun _=>T.z) (fun _=>T.unitPos) (BitDescription.scannedRows he T).fit
          (BitDescription.scannedRows he T).pack ((BitDescription.scannedRows he T).profile choice)
          (scanKey he T choice col same) hub k g q old used cut)
        (scanOrdinals he T)
  | named {S : MarkedWorld F d P bits} (n : Normalize S) (t : Tape n.result.graph.Edge) {pair : ScanNumbers he T}
      (kept : IssuedRows he T choice oldID rootRank S n t pair) (site : n.result.graph.Site↪ℕ) :
      IssuedRows he T choice oldID rootRank S
        (n.appendNames (DescentPhysicalOrder.rename site)
          (DescentPhysicalOrder.rename (t.sourceKey n.result.graph.src site n.result.graph.width)))
        (Tape.afterNames n t (DescentPhysicalOrder.rename site)
          (DescentPhysicalOrder.rename (t.sourceKey n.result.graph.src site n.result.graph.width)))
        pair

variable {he T choice oldID rootRank}
theorem IssuedRows.toIssued {S : MarkedWorld F d P bits} {n : Normalize S} {t : Tape n.result.graph.Edge}
    {pair : ScanNumbers he T} (issued : IssuedRows he T choice oldID rootRank S n t pair) :
    Issued W G oldID rootRank S n t := by
  induction issued with
  | stage col same hub k g q legal source old used cut=>
    exact Issued.stage home color T.cap col same constantZ (fun _=>T.unitPos) (scan).fit ((scan).profile choice)
      hub k g q legal old used cut
  | named n t kept site ih=>exact Issued.named n t ih site

theorem IssuedRows.sourceNumbers {S : MarkedWorld F d P bits} {n : Normalize S} {t : Tape n.result.graph.Edge}
    {pair : ScanNumbers he T} (issued : IssuedRows he T choice oldID rootRank S n t pair) :
    ∃rank : T.V↪ℕ, HEq rank rootRank ∧ pair=nativeNumbers he T rank := by
  induction issued with
  | stage col same hub k g q legal source old used cut=>exact source.1
  | named n t kept site ih=>exact ih

theorem IssuedRows.numbers_eq {S : MarkedWorld F d P bits} {n : Normalize S} {t : Tape n.result.graph.Edge}
    {pair : ScanNumbers he T} (issued : IssuedRows he T choice oldID rootRank S n t pair)
    (r : T.V↪ℕ) (root : HEq r rootRank) : pair=nativeNumbers he T r := by
  obtain ⟨rank,same,read⟩ := issued.sourceNumbers
  obtain rfl := eq_of_heq (same.trans root.symm)
  exact read

theorem IssuedRows.siblings {c₁ c₂ : (T.result he).Choice} {S₁ S₂ : MarkedWorld F d P bits}
    {n₁ : Normalize S₁} {n₂ : Normalize S₂} {t₁ : Tape n₁.result.graph.Edge} {t₂ : Tape n₂.result.graph.Edge}
    {r₁ r₂ : ScanNumbers he T} (left : IssuedRows he T c₁ oldID rootRank S₁ n₁ t₁ r₁)
    (right : IssuedRows he T c₂ oldID rootRank S₂ n₂ t₂ r₂) : r₁=r₂ := by
  obtain ⟨rank,hr,hl⟩ := left.sourceNumbers
  exact hl.trans (right.numbers_eq rank hr).symm

/-- Decode the ordinary successor's actual scalar nodes using precisely
the pair table number that was issued with its sparse cable tape. -/
def IssuedRows.nodeOrder {n : Normalize ((T.result he).state choice)} {t : Tape n.result.graph.Edge}
    {pair : ScanNumbers he T} (_issued : IssuedRows he T choice oldID rootRank _ n t pair)
    (B : BitDescription W) {oldSize : ℕ} (old : NodeOrder.All B ≃ Fin oldSize) :
    NodeOrder.All (BitDescription.follow n (BitDescription.scanned he T B choice)) ≃
      Fin (oldSize+Fintype.card (scan).pairs*6) :=
  (NodeOrder.followNames n _).trans (NodeOrder.scannedOrdinal B he T choice old pair)

end
end Hierarchy.DescentStageEdgeReceipt

end OAI
