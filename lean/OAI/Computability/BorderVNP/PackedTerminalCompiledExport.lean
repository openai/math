import OAI.Computability.BorderVNP.PackedTerminalCompiledNames
import OAI.Computability.BorderVNP.PackedTerminalSewnHistory

/-! # Native geometry export of the selected outer machine above the true wired grid

The original immutable description and exterior pointers are computed by
the public schedule. The accepted histogram supplies the dynamic terminal
routes, and its attached grouped ports identify all final cable endpoints.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicCapacity Shortening.PreparedBins
open BorderVNP.Epoch BorderVNP.Epoch.Round Packing TeamContraction
open Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts Diagonal.ExternalSew.RowTrace
open EnrichedOuter EnrichedOuter.Boundary TerminalCells Inherited.WorkWords
open VPVNP VPVNP.BurstRAM VPVNP.VerifierNetwork RoutingISA GeometryFrameEncoding DiagonalResidueRAM
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {R r t pins link inner n d copies w T : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} {deep : S.floor+1+S.drop*T ≤ d+1}
    (compiled : Compiled (fun _ : Fin (tileCount (Fintype.card (Cube D)) d) =>
      copies*inputBlockWidth r n (Fintype.card (Cube D)) d) deep budget cap w)
    (leaf : Admissible (Good (S:=S) (start:=d+1) (shape:=boundaryShape S (d+1)) (w:=w)
      (bits:=fun _ : Fin (tileCount (Fintype.card (Cube D)) d) => copies*inputBlockWidth r n (Fintype.card (Cube D)) d)
      budget) 0)
    {X : Type} [Fintype X] (base : VerifierNetwork.Frame X (Boundary.Pins S (d+1) (boundary S (d+1)) w 0)) (x : X → Bool)
    (baseValue : base.eval x = leaf.val.words)
    (grid : ∀ i, (leaf.val.rows.site (leaf.val.pack.layout.attach i)).val = i.val)
    {b C active reserve native o : ℕ}

local notation "tileN" => tileCount (Fintype.card (Cube D)) d
local notation "block" => inputBlockWidth r n (Fintype.card (Cube D)) d
local notation "sh" => boundaryShape S (d+1) T
local notation "leaves" => repeatLeaf (fan S) leaf T
local notation "guess" => Slot (fan S) (Machine.Guess S (d+1) (fun _ _ => w)) T
local notation "off" => flatOffset (compiledOffset S (d+1)) T
local notation "Γ" => (X ⊕ Fin reserve) ⊕ Pins S (d+1) (boundaryShape S (d+1)) w T
local notation "Z" => Wires (allowedMoves (Cube D) S.budget) (Fintype.card (Cube D))
    (EnrichedOuter.depth S (d+1) T) (Shape.sites (boundaryShape S (d+1) T)) (Shape.edges (boundaryShape S (d+1) T)) w b

include baseValue grid in
set_option maxRecDepth 6000 in
set_option maxHeartbeats 1800000 in
/-- All native row outputs for the true selected grid branch, with fixed
source IDs and no separate field-correctness or endpoint oracle. -/
theorem compiled_grid_export (count : (fan S)^T*copies = R+1)
    (number : (Cube D → Deck (EnrichedOuter.depth S (d+1) T+1)) ≃ Fin C)
    (positive : 0<(sh).sites) (vf : (sh).sites ≤ 2^w) (cf : C ≤ 2^b)
    (blockPos : 0<block) (blockSmall : block≤link) (pw : copies*block<2^w) (hb : b≤w) (hw : w≤native)
    (ord : guess ≃ Fin active) (fits : active ≤ reserve) (word : Fin reserve → Bool)
    (aux : VerifierNetwork.Frame Γ (Fin (sh).sites × Fin w)) (rest : VerifierNetwork.Frame (Z ⊕ Bool) (Outputs o w))
    (q : (compiled.machine.system.histories T le_rfl leaves).Index)
    (selected : readProfile ord fits word = encode compiled.machine.codec T le_rfl leaves q)
    {pub : Arg → Word native} {mac : TeamOpcode.Macros native 8} {bank after : Bank native}
    {mem result : Memory native} {fresh dest clock : ℕ} {es : List (TeamRAM.Event native)} :
    let s := (state (S:=compiled.machine.system) T le_rfl leaves q).val
    let N := (flattenPack T s.pack).layout
    let host := attachedHosts G Fintype.card_pos count N
    let p : FieldExport.Params := ⟨R,r,G.program.length+t,link,block,tileN⟩
    let hp : p.Valid := ⟨blockPos,blockSmall,gridRoom G Fintype.card_pos⟩
    let original := originalPins (tiles:=tileN) positive off
    let F := TerminalCells.fields (Move:=allowedMoves (Cube D) S.budget) (q:=Fintype.card (Cube D))
      (d:=EnrichedOuter.depth S (d+1) T) (E:=(sh).edges) vf cf (groupRow (tiles:=tileN) off) (fun _ => copies*block)
    let B := FieldExport.fields F p (attachedName off copies)
    let src := FieldExport.withSewnFields (boundFrame (factorEnum D) number cf (VerifierNetwork.Frame.initial Sum.inr) aux)
    let hist := compile compiled.machine.steps T le_rfl (repeatLeaf (fan S) base T)
    let y := Sum.elim (Sum.elim x word) (fun j => hist.eval (Sum.elim x (readProfile ord fits word)) (.inl j))
    let emit := terminalEmitter B hb original id rest src
    ∀ size : N.Site → ℕ, Covers s.rows.site size aux y →
    GeometryReturn pub mac bank mem fresh dest clock (emittedWords hist ord fits emit x word) es after result →
      (∀ z : Fin ((fan S)^T) × Fin tileN, original (finProdFinEquiv z) = s.rows.site (N.attach z)) ∧
      CellAddressPhysical.Represents (FieldExport.finalLayout p host)
        (fun v => number (reduceMove (EnrichedOuter.depth S (d+1) T) (s.route.origin v))) size s.rows.site
        (FieldExport.mergedEdges p hp s.rows.edge) finProdFinEquiv.toEmbedding B (src.eval y) ∧
      RoutingISA.Runs pub mac GeometryAdvice.reconstruct bank mem es after result ∧ traceCost es ≤ clock ∧
      RoutingOutputs.Image B original id (src.eval y) dest (readings result) ∧
      (∀ i : Fin o, result (dest+((sh).edges+p.slots)*3+
        RoutingOutputs.count ((sh).edges+p.slots) C ((fan S)^T*tileN) ((R+1)*tileN)+i.val) =
        DiagonalResidueRAM.word native (ParseBatchSort.value fun j => rest.eval (src.eval y) (.inl (i,j)))) ∧
      ∀ a < fresh, result a = mem a := by
  intro s N host p hp original F B src hist y emit size covers run
  have named (z : Fin ((fan S)^T) × Fin tileN) : (s.rows.site (N.attach z)).val = off z.1+z.2.val :=
    compiledRepeated_gridRow compiled leaf grid T le_rfl q z
  have orig (z : Fin ((fan S)^T) × Fin tileN) : original (finProdFinEquiv z) = s.rows.site (N.attach z) :=
    originalPin_value positive off z _ (named z).symm
  have labels := attached_name G Fintype.card_pos count N s.rows.site off named
  have copiesPos : 0<copies := Nat.pos_of_ne_zero (fun h => by rw [h,Nat.mul_zero] at count; omega)
  have blockFit : block < 2^w := (Nat.le_mul_of_pos_left _ copiesPos).trans_lt pw
  exact ⟨orig,Machine.checked_sewn_image compiled.machine leaf base x baseValue number vf cf pw hb hw ord fits word
    off aux q selected p hp blockFit (groupedLane G tileN Fintype.card_pos ((fan S)^T) copies count)
    (attachedName off copies) original rest (fun z => (named z).symm) size covers host
    (fun u i hi => (labels u i hi).trans (by rfl)) run⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
