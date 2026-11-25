import OAI.Hierarchy.DescentPackedStageRun
import OAI.Hierarchy.DescentPackedPhaseResident

namespace OAI
/-! # A measured stage entered from the public chronology and true predecessor records -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentPackedColony DescentColonies DescentGL DescentBinaryField DescentAffineColors StarKeys DescentHostDirectory
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {C L k ℓ Δ d b w hBits : ℕ} {J V F P : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {p ε : ℝ}
variable (A : GroupStage W G p ε J V k) (ej : J≃Fin C) (ev : V≃Fin L) (h : L≤2^ℓ)
local notation "fee" => A.wire*(A.z*G.b)
local notation "D" => DescentHostDegree.gap A.degree
local notation "a" => DescentHostDegree.packExponent 20 A.degree
local notation "cap" => 2^a*(fee*A.cap)
local notation "full" => W.siteUnits (fun v => A.hub (Prod.snd (A.pos v))) A.records A.wire 256 A.hist
local notation "outgoing" => fun v : W.graph.Site => Finset.card (Finset.filter (fun edge => W.graph.src edge = v) W.core)
local notation "wt" => (fun g=>Padded.table (H:=2^ℓ) (A.groupedCounts ej ev full g))
local notation "amt" => (fun g=>Padded.table (H:=2^ℓ) (A.groupedCounts ej ev outgoing g))
local notation "M" => lanes hBits (Phase.unit k b)

theorem run_packed_chart (he : 0≤ε) (chart : Frame.Chart) (marked : Bank) (rs : DynamicSplit.Roster ℓ Δ)
    (members : ∀i j,j∈DynamicSplit.incoming rs i ↔ ∃v z:V,i=(ev v).castLE h ∧ j=(ev z).castLE h ∧ v∈A.near z)
    (layout : Phase.Arena.Room chart marked Δ k b hBits w (2^ℓ) C)
    (K : ℕ) (hardware : w≤K*hBits)
    (short : fee*A.cap<2^b) (leaves : C*2^ℓ*2^k<2^w) (budget : W.core.card<2^w)
    (m : Memory w) (loaded : (Phase.Arena.image chart A.fieldBits Δ (2^ℓ) C b hBits D cap).Resident m)
    (roster : ∀v i,m (chart.roster.base+(v.val*Δ+i.val))=(target (rs v i):Word w))
    (weights : Reads chart.weights (fun v g=>counts b (wt g v)) M m)
    (outgoingRows : Reads marked (fun v g=>counts b (amt g v)) M m) :
    let S:=Phase.Arena.shelves chart marked Δ k b hBits
    ∃out : Memory w,∃i : Fin (2^k-1),∃j : Candidate k,∃hm : 0<M,
      (Phase.program S w (2^ℓ) C M).Exec m out (Phase.cost S w (2^ℓ) C M) ∧
      Phase.cost S w (2^ℓ) C M*w≤K*(Phase.factor k Δ*(hBits+2^ℓ*hBits+4*2^ℓ*C*Phase.unit k b)) ∧
      IsScannedAt W G A.pos A.block (fun v=>A.hub (A.pos v).2) A.records A.wire A.hist A.z A.cap A.degree
        (groupedNear A.near) A.fieldBits A.small (A.stage.result he) (seedAt k i) (linear j) (offset j) ∧
      out S.mu=(i.val:Word w) ∧ out S.paint=(j.val:Word w) ∧ (∀u<S.first,out u=m u) ∧
      (∀u,S.output+2^k*(2^ℓ*chunks C M)≤u→ out u=m u) ∧
      seedAt k i=(DescentKernelHistory.BitDescription.scannedRows he A.stage).μ ∧
      j=code (DescentKernelHistory.BitDescription.scannedRows he A.stage).α (DescentKernelHistory.BitDescription.scannedRows he A.stage).β ∧
      A.WinnerWords ej ev rs M S.output i j out ∧
      ∀u : W.graph.Site,
        let blk:=reindexedBlock W.graph A.block (multiplier A.fieldBits (seedAt k i))
        let fit:=small_reindexed W.graph A.pos A.block full A.small (multiplier A.fieldBits (seedAt k i))
        let home:=occupiedHome W.graph A.pos blk full (groupedNear A.near) D a (fee*A.cap) fit
        let whereAt:=occupiedAddress W.graph (fee*A.cap) (groupedNear A.near) D a (blockMass W.graph A.pos blk full) fit A.pos blk
        let v:=(ev (A.pos u).2).castLE h
        let g:=ej (A.pos u).1
        let pos:=PackedWinnerRAM.slot S.output (2^ℓ*chunks C M) (A.block u)+(row (2^ℓ) C M (position v g hm)).val
        let cell:=whereAt (home u)
        digit (k+3) (lane g hm).val (out pos).val=1+2*(2^cell.2.1-1+cell.2.2)+(thick j (blk u)).toNat := by
  exact A.packed_ordinary ej ev h he _ rs members (Phase.Arena.space chart marked A.fieldBits (2^ℓ) C layout)
    layout.wide layout.embed K hardware short leaves budget m
    (Phase.Arena.initial_resident chart marked A.fieldBits D cap layout rs wt amt m loaded roster weights outgoingRows)

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
