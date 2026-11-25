import OAI.Hierarchy.DescentIssuedNodeOrder
import OAI.Hierarchy.DescentNormalizationNames

namespace OAI
/-! # The single source-ordered physical renaming of a measured ordinary stage -/
namespace Hierarchy.DescentStageEdgeReceipt
open DescentSixParty DescentSixParty.StarKeys DescentHostDirectory DescentKernelHistory
open scoped Classical BigOperators
noncomputable section
variable {F P H : Type} [Field F] [Fintype H] [DecidableEq H]
variable {d : ℕ} {bits : P→ℕ} {u ε : ℝ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {he : 0≤ε} {T : StageInput W G u ε} {choice : (T.result he).Choice}
variable {oldID : W.graph.Edge ↪ Fin (Fintype.card W.graph.Edge)} {rootRank : H ↪ ℕ}

abbrev SignedClaim (he : 0≤ε) (T : StageInput W G u ε) :=
  (S : MarkedWorld F d P bits)→(n : Normalize S)→Tape n.result.graph.Edge→ScanNumbers he T→Prop

/-- The geometric case of an ordinary step, with its actual raw-parent tape and the
simultaneous physical permutations chosen before the following measured stage. -/
def AtSignedStage (he : 0≤ε) (T : StageInput W G u ε) (choice : (T.result he).Choice)
    (oldID : W.graph.Edge ↪ Fin (Fintype.card W.graph.Edge)) (rootRank : H ↪ ℕ)
    (Q : SignedClaim he T) : Prop :=
  ∀ (col : ScanColonies he T ↪ H×(ℕ×ℕ))
      (same : ∀e∈W.core,scanColorAt he T (W.graph.src e)=scanColorAt he T (W.graph.dst e))
      (hub : H→Bool) (k g q : ℕ) (_legal : ∀c,thickKey (col c)∈keys k 1)
      (_source : (∃rank : T.V↪ℕ, HEq rank rootRank ∧
        DescentPacking.PairRAM.globalNumberBy W.graph W.core (scanHomeAt he T) (scanColorAt he T) T.cap
          (DescentPacking.originalId (ScanColonies he T))=nativeNumbers he T rank) ∧
        k=T.k ∧ g=DescentHostDegree.gainExponent 20 T.Δ ∧
        (∀v,nativeKey W.graph W.core (scanHomeAt he T) (scanColorAt he T) T.cap col same
          (bestLayout (branchWidth G (fun _=>T.z) ((BitDescription.scannedRows he T).profile choice))) v∈
          keys T.k (2^(DescentHostDegree.packExponent 20 T.Δ)+2)) ∧ HEq col (nativeAddress he T) ∧
        (∀ci,(col ci).2=(nativeAddress he T ci).2) ∧
        ∀u,HEq (col (scanHomeAt he T u)).1 (T.pos u) ∧ hub (col (scanHomeAt he T u)).1=T.hub u)
      (old : ∀e∈W.core,q∣W.graph.width e) (used : ∀j,(BitDescription.scannedRows he T).pick j∈W.core)
      (cut : ∀_i : (BitDescription.scannedRows he T).pairs,q∣T.z),
      let p:=(BitDescription.scannedRows he T).profile choice
      let key:=nativeKey W.graph W.core (scanHomeAt he T) (scanColorAt he T) T.cap col same (bestLayout (branchWidth G (fun _=>T.z) p))
      let pair:=DescentPacking.PairRAM.globalNumberBy W.graph W.core (scanHomeAt he T) (scanColorAt he T) T.cap (DescentPacking.originalId (ScanColonies he T))
      let norm:=W.subroundNormalize G (BitDescription.scannedRows he T).pick (fun _=>T.z) (fun _=>T.unitPos) (BitDescription.scannedRows he T).fit (BitDescription.scannedRows he T).pack p
        key hub k g q old used cut
      let tape:=ordinary W G oldID pair (BitDescription.scannedRows he T).pick (fun _=>T.z) (fun _=>T.unitPos) (BitDescription.scannedRows he T).fit (BitDescription.scannedRows he T).pack p
        key hub k g q old used cut
      ∀ site : norm.result.graph.Site↪ℕ,
        let vs:=DescentPhysicalOrder.rename site
        let es:=DescentPhysicalOrder.rename (tape.sourceKey norm.result.graph.src site norm.result.graph.width)
        Q _ (norm.appendNames vs es) (Tape.afterNames norm tape vs es) pair

/-- An issued single-renaming step has exactly the raw shape used by the signed
parent windows. Dependent claims may mention its normalized graph and tape. -/
theorem IssuedRows.signedCases {S : MarkedWorld F d P bits} {n : Normalize S}
    {t : Tape n.result.graph.Edge} {pair : ScanNumbers he T}
    (issued : IssuedRows he T choice oldID rootRank S n t pair) (one : n.nameCount=1)
    {Q : SignedClaim he T} (stageCase : AtSignedStage he T choice oldID rootRank Q) :
    Q S n t pair := by
  cases issued with
  | stage col same hub k g q legal source old used cut =>
    change (0:ℕ)=1 at one
    omega
  | named prior raw kept site =>
    have zero : prior.nameCount=0 := by
      rw [Normalize.nameCount_append] at one
      omega
    cases kept with
    | stage col same hub k g q legal source old used cut =>
      exact stageCase col same hub k g q legal source old used cut site
    | named n' t' kept' site' =>
      rw [Normalize.nameCount_append] at zero
      omega

end
end Hierarchy.DescentStageEdgeReceipt

end OAI
