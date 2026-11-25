import OAI.Hierarchy.DescentBoundedWorldHistory
import OAI.Hierarchy.DescentMeasuredEpoch

namespace OAI
/-! # Actual physical branch histories through an arbitrary finite shrink schedule -/

namespace Hierarchy.DescentKernelHistory.BitDescription
open Computability.BorderVNP.Crossing DescentSixParty
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {u ε : ℝ} (he : 0≤ε)
variable {G : PoweredGadget F}
variable {W : MarkedWorld F d P bits} (T : StageInput W G u ε) (B : BitDescription W)

open DescentColonies DescentGL DescentWalshTables DescentPacking StarKeys
local notation "measure" => W.siteUnits T.hub T.records T.wire 256 T.hist
local notation "unit" => T.wire*(T.z*G.b)

def scanBlocks (μ : Nonzero T.k) := reindexedBlock W.graph T.block (multiplier T.fieldBits μ)
def scanHome (μ : Nonzero T.k) := occupiedHome W.graph T.pos (scanBlocks T μ) measure T.near
  (DescentHostDegree.gap T.Δ) (DescentHostDegree.packExponent 20 T.Δ) (unit*T.cap)
  (small_reindexed W.graph T.pos T.block measure T.small (multiplier T.fieldBits μ))
def scanColor (μ : Nonzero T.k) (α : DescentWalshTables.Bits T.k) (β : ZMod 2) (v : W.graph.Site) :=
  decide (binaryRow α ((address T.k).symm (scanBlocks T μ v))+β=0)

abbrev scanPairs (μ : Nonzero T.k) (α : DescentWalshTables.Bits T.k) (β : ZMod 2) :=
  NativePair W.graph W.core (scanHome T μ) (scanColor T μ α β) T.cap
abbrev scanPick (μ : Nonzero T.k) (α : DescentWalshTables.Bits T.k) (β : ZMod 2) :
    (scanPairs T μ α β × Fin 2) ↪ W.graph.Edge :=
  colorPick W.graph W.core (scanHome T μ) (scanColor T μ α β) T.cap
abbrev scanPack (μ : Nonzero T.k) (α : DescentWalshTables.Bits T.k) (β : ZMod 2) :=
  coloredPack W.graph W.core (scanHome T μ) (scanColor T μ α β) T.cap

set_option maxHeartbeats 1200000 in
structure ScanRows where
  μ : Nonzero T.k
  α : DescentWalshTables.Bits T.k
  β : ZMod 2
  native : IsScannedAt W G T.pos T.block T.hub T.records T.wire T.hist T.z T.cap T.Δ T.near
    T.fieldBits T.small (T.result he) μ α β
  firstPaint : FirstPaint W.graph W.core T.pos (scanBlocks T μ) measure T.near (DescentHostDegree.gap T.Δ)
    (DescentHostDegree.packExponent 20 T.Δ) T.cap unit
    (small_reindexed W.graph T.pos T.block measure T.small (multiplier T.fieldBits μ)) (DescentAffineColors.code α β)
  fit : ∀ (i : scanPairs T μ α β) (s : Fin 2),W.graph.width (scanPick T μ α β (i,s))=T.z*G.b
  profile : (T.result he).Choice ≃ (scanPairs T μ α β→Profile G.C)
  state : ∀ (p : (T.result he).Choice),(T.result he).state p=W.selected (I:=scanPairs T μ α β)
    G (scanPick T μ α β) (fun _=>T.z) (fun _=>T.unitPos)
    fit (scanPack T μ α β) (profile p)

/-- Select a single measured native paint for the entire family of coefficient choices. -/
def scannedRows : ScanRows he T := Classical.choice (by
  obtain ⟨μ,α,β,actual,paint⟩ := T.result_scanned he
  obtain ⟨winner,hz,fit,profile,state⟩ := actual
  exact ⟨⟨μ,α,β,⟨winner,hz,fit,profile,state⟩,paint,fit,profile,state⟩⟩)

namespace ScanRows
variable {G : PoweredGadget F} {he : 0≤ε} {T : StageInput W G u ε}
abbrev pairs (r : ScanRows he T) := scanPairs T r.μ r.α r.β
abbrev pick (r : ScanRows he T) := scanPick T r.μ r.α r.β
abbrev pack (r : ScanRows he T) := scanPack T r.μ r.α r.β
theorem picked (r : ScanRows he T) (i : r.pairs×Fin 2) : r.pick i∈W.core :=
  by
    unfold pick scanPick colorPick
    apply pairedCore_mem
end ScanRows

/-- The bit description is transported along the exact world identity published
by the coefficient selection. The multiplier and paint are shared by all profiles. -/
def scanned (p : (T.result he).Choice) : BitDescription ((T.result he).state p) :=
  let r := scannedRows he T
  cast (congrArg BitDescription (r.state p).symm) (B.selected G r.pick (fun _=>T.z) (fun _=>T.unitPos) r.fit
    (fun _=>le_refl T.z) r.pack (r.profile p))

theorem scanned_anchor (p : (T.result he).Choice) :
    let r := scannedRows he T
    HEq (scanned he T B p) (B.selected G r.pick (fun _=>T.z) (fun _=>T.unitPos) r.fit
      (fun _=>le_refl T.z) r.pack (r.profile p)) := by
  dsimp only [scanned]
  exact cast_heq _ _

def extend (H : Histories F d P bits) (data : SubroundInput H G (u:=u) he)
    (b : ∀c,BitDescription (H.state c)) (f : (H.extend he data).Choice) :
    BitDescription ((H.extend he data).state f) :=
  follow (data.reblock f.1 f.2) (scanned he (data.placement f.1) (b f.1) f.2)

def schedule {t : ℕ} {H : Histories F d P bits} (plan : Schedule G (u:=u) he t H)
    (old : ∀c,BitDescription (H.state c)) (f : (Schedule.finish G he plan).Choice) :
    BitDescription ((Schedule.finish G he plan).state f) :=
  match t,H,plan,f with
  | 0,_,_,f=>old f
  | _+1,H,⟨data,remaining⟩,f=>schedule remaining (extend he H data old) f

end
end Hierarchy.DescentKernelHistory.BitDescription

end OAI
