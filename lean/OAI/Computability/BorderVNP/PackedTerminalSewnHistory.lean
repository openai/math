import OAI.Computability.BorderVNP.PackedTerminalHistoryFields
import OAI.Computability.BorderVNP.PackedTerminalRoutingReturn
import OAI.Computability.BorderVNP.PackedRoutingSewn

/-! # Sewn geometry arrays on the native accepted histogram

The row-major count broadcast, the current routed network and the native
array outputs all refer to one history. The edge rows include the stable
four-slot exterior intervals as well as the old compressed cables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicCapacity Shortening.PreparedBins
open BorderVNP.Epoch BorderVNP.Epoch.Round Packing TerminalCells Inherited.WorkWords
open VPVNP VPVNP.BurstRAM VPVNP.VerifierNetwork RoutingISA GeometryFrameEncoding DiagonalResidueRAM
open Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {tiles pw start T w C b : ℕ} {shape : ℕ → Shape} {budget : ℕ → ℕ}
    {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {iw : ℕ → ℕ → ℕ}
    {deep : S.floor+1+S.drop*T ≤ start}
variable (M : Machine deep (Boundary.Good (S:=S) (start:=start) (shape:=shape) (w:=w)
    (bits:=fun _ : Fin tiles => pw) budget) V iw)
    (leaf : Admissible (Boundary.Good (S:=S) (start:=start) (shape:=shape) (w:=w)
      (bits:=fun _ : Fin tiles => pw) budget) 0)
    {X : Type} [Fintype X] (bottom : VerifierNetwork.Frame X (Boundary.Pins S start shape w 0))
    (x : X → Bool) (base : bottom.eval x = leaf.val.words)
    {active reserve J o native : ℕ}
local notation "guessType" => Slot (fan S) (Guess S start iw) T
local notation "tree" => repeatLeaf (fan S) bottom T
local notation "leaves" => repeatLeaf (fan S) leaf T
local notation "Γ" => (X ⊕ Fin reserve) ⊕ Boundary.Pins S start shape w T
local notation "Z" => TerminalCells.Wires (allowedMoves (Cube D) S.budget) (Fintype.card (Cube D))
    (depth S start T) (Shape.sites (shape T)) (Shape.edges (shape T)) w b

include base in
/-- Exact correspondence of the mathematical sewn network with the physical
cable, delivery placement and cell-offset words at the end of the signed
processor's geometry phase. Its raw profile is the one read from the
reserved broadcast, including the canonical tail checked by the interpreter. -/
theorem checked_sewn_image (number : (Cube D → Deck (depth S start T+1)) ≃ Fin C)
    (vf : (shape T).sites ≤ 2^w) (cf : C ≤ 2^b) (width : pw < 2^w) (hb : b ≤ w) (hw : w ≤ native)
    (ord : guessType ≃ Fin active) (fit : active ≤ reserve) (word : Fin reserve → Bool)
    (offs : Fin ((fan S)^T) → ℕ) (aux : VerifierNetwork.Frame Γ (Fin (shape T).sites × Fin w))
    (q : (M.system.histories T le_rfl leaves).Index)
    (selected : readProfile ord fit word = encode M.codec T le_rfl leaves q)
    (p : Params) (hp : p.Valid) (gWidth : p.g < 2^w)
    {P : Type} (lane : P ↪ Σ _ : Fin ((fan S)^T) × Fin tiles, Fin pw)
    {phys : PublicPort p.R p.processors p.literal p.link ≃ P}
    (name : ℕ → ℕ → ℕ) (original : Fin J → Fin (shape T).sites)
    (rest : VerifierNetwork.Frame (Z ⊕ Bool) (Outputs o w))
    {pub : Arg → Word native} {mac : TeamOpcode.Macros native 8} {bank after : Bank native} {mem result : Memory native}
    {fresh dest clock : ℕ} {es : List (TeamRAM.Event native)} :
    let s := (state (S:=M.system) T le_rfl leaves q).val
    let N := (flattenPack T s.pack).layout
    let raw := Sum.elim x word
    let g := readProfile ord fit word
    let y := Sum.elim raw (output M.steps T le_rfl tree x g)
    let F := TerminalCells.fields (Move:=allowedMoves (Cube D) S.budget) (q:=Fintype.card (Cube D))
      (d:=depth S start T) (E:=(shape T).edges) vf cf (groupRow (tiles:=tiles) offs) (fun _ => pw)
    let source := boundFrame (factorEnum D) number cf (VerifierNetwork.Frame.initial Sum.inr) aux
    let B := FieldExport.fields F p name
    let newSource := withSewnFields source
    let emit := terminalEmitter B hb original id rest newSource
    let hist := compile M.steps T le_rfl tree
    (∀ z : Fin ((fan S)^T) × Fin tiles, offs z.1+z.2.val = (s.rows.site (N.attach z)).val) →
    ∀ (size : N.Site → ℕ), Covers s.rows.site size aux y →
    ∀ h : BlockHosts (FineView.layout N lane) phys p.g,
    (∀ (u : Fin (p.R+1)) i, i < p.sites → name u.val i = (F.sites (s.rows.site (h.host (u,i)))).val) →
    GeometryReturn pub mac bank mem fresh dest clock (emittedWords hist ord fit emit x word) es after result →
      Packing.CellAddressPhysical.Represents (finalLayout p h)
        (fun v => number (reduceMove (depth S start T) (s.route.origin v))) size
        s.rows.site (mergedEdges p hp s.rows.edge) finProdFinEquiv.toEmbedding B (newSource.eval y) ∧
      RoutingISA.Runs pub mac GeometryAdvice.reconstruct bank mem es after result ∧ traceCost es ≤ clock ∧
      RoutingOutputs.Image B original id (newSource.eval y) dest (readings result) ∧
      (∀ i : Fin o, result (dest+((shape T).edges+p.slots)*3+
        RoutingOutputs.count ((shape T).edges+p.slots) C J ((p.R+1)*p.sites)+i.val) =
        DiagonalResidueRAM.word native (ParseBatchSort.value fun j => rest.eval (newSource.eval y) (.inl (i,j)))) ∧
      ∀ a < fresh, result a = mem a := by
  intro s N raw g y F source B newSource emit hist originalNames size covered hosts hostNames run
  have checked := checked_fields M leaf bottom x base number vf cf width offs raw aux q g selected originalNames size covered
  have sewn := frame_represents p hp N lane hosts _ size s.rows.site s.rows.edge finProdFinEquiv.toEmbedding
    F source y checked.2 name hostNames gWidth
  exact ⟨sewn,GeometryReturn.routing_image hist ord fit B hb hw original id rest newSource x word run⟩

end PackedHistoryCircuit.Normalized.EnrichedOuter.Machine

end BorderVNP
end Computability
end OAI
