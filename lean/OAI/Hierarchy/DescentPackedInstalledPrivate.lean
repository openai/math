import OAI.Hierarchy.DescentMixedPrivateRoots

namespace OAI
/-! # Scanning actual coarse group rows and relative root roles to publish installed cables -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments DescentResetCableSlots DescentRouterSlots DescentMixedRouter
open DescentPackedPrivateMenu DescentSIMDLookup DescentPackedFallbackTree.Image DescentPacking.PackedMatch.Local.Gather DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready))
    (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frm : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u=>(A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "X" => Z.placement
local notation "arr" => leafPanel A S ready digits native Z T frm
local notation "cnt" => (2^(m-T.commonDepth)*(2*A.cap))
local notation "r" => (Z.k-T.commonDepth)
local notation "groupCount" => (2^T.commonDepth:ℕ)
local notation "menu" => selected (X) Z.graph Z.positive Z.pay Z.circuit
local notation "dev" => DescentMixedRouter.device Z.graph Z.positive Z.unit (X).contact (X).input (X).site (X).owner (X).align (D:=d)
local notation "slot" => privateWire (X) Ht T.bookHeight Z.graph Z.positive Z.pay Z.circuit d
local notation "cap" => max (Fintype.card (DescentCommonPalette.rotor Z.graph).Edge) (2^(Ht+1))
local notation "l" => Z.layerBits
local notation "operandBits" => digitBits Z.n r Ht cnt l
local notation "outputBits" => DescentPackedPrivateMenu.fieldBits Z.graph r Ht cnt l C Z.width
local notation "panelWidth" => (outputBits*(cap*5))

/-- The output for any moving edge is selected by the actual actor's old host, common block,
local gate family and its physical slot. Incoming long IDs and absolute widths occur only in the
interpretation of this compressed archive. -/
theorem issued_private {hosts M w : ℕ} (vertex : Z.V↪Fin hosts) (unit : 0<Z.unit)
    (side : Bool) (ticket : Z.RootTicket T) (tables : Fin 5→Tables) («fields» : Fin 5→Expr)
    (B : DescentSIMDLookup.Banks) (mid out : ℕ) (positive : 0<M) (mem : Memory w)
    (bounds : Bounds (w:=w) (d:=operandBits) (M:=M) tables «fields» mid)
    (columnLaw : ∀j,Static (tables j) (setField (d:=operandBits) j) M mem)
    (incoming : ∀j,Source («fields» j) (fun v i=>DescentPackedPrivateMenu.payload r Ht cnt l
        (Z.rootsOf T vertex unit side (arr side) ticket v i) j) M mem)
    (midFits : mid+hosts*chunks groupCount M<2^w) (fit : DescentSIMDLookup.Fits B (operandBits*5) panelWidth M hosts groupCount w out)
    (rom : resident (fused Z.graph r Ht cnt l C Z.width cap side) B hosts groupCount M mem)
    (romBelow : B.dictionary.base+2^((operandBits*5)*M)≤ mid) (maskBelow : B.mask.base+hosts*chunks groupCount M≤ mid)
    (fromGather : B.source.base=mid) :
    let act:=gatherFields tables «fields»
    let rows:=hosts*chunks groupCount M
    let dst:=imageBank hosts groupCount M out B (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program B out hosts groupCount M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
      ∀(g : (X).Site),Z.rootTicket T g=ticket →∀e : (dev (menu side g)).Edge,
        let block:=Z.rootBlock T g
        let addr:=row hosts groupCount M (position (vertex (Z.rootVertex T g)) block positive)
        let owner:=digit panelWidth (lane block positive).val (dst (out+addr.val)).val
        Z.expand T vertex g (fun j=>digit outputBits (finProdFinEquiv (slot (side,g) e,j)).val owner)=
          Z.actualRecord T vertex (Z.privateWireAt T side g e) := by
  let x:=Z.rootsOf T vertex unit side (arr side) ticket
  obtain ⟨run,read⟩:=DescentPackedPrivateMenu.issued Z.graph r Ht cnt l C Z.width cap side tables «fields» B mid out
    x positive mem bounds columnLaw incoming midFits fit rom romBelow maskBelow fromGather
  refine ⟨run,?_⟩
  intro g filtered e
  let v:=vertex (Z.rootVertex T g)
  let block:=Z.rootBlock T g
  have cell:=fun j=>read v block (slot (side,g) e) j
  have atRoot := (congrArg (fun key => Z.rootsOf T vertex unit side (arr side) key v block) filtered.symm).trans
    (Z.rootsOf_read T vertex unit side (arr side) g)
  dsimp only
  apply Eq.trans (congrArg (Z.expand T vertex g) (funext cell))
  dsimp only [x]
  rw [atRoot]
  cases g with
  | inl g=>exact Z.rotor_row T vertex unit cnt side g e
  | inr t=>exact tree_row A S ready digits native Z T frm vertex side t e

/-- Exact frame of the two writes exposed in the physical issuer. The same old input panels can
be read by all subsequent relative root and side passes. -/
theorem issued_private_frame {hosts groups M w : ℕ} (tables : Fin 5→Tables) («fields» : Fin 5→Expr)
    (B : DescentSIMDLookup.Banks) (mid out : ℕ) (mem : Memory w) (addr : ℕ)
    (a : addr< mid ∨ mid+hosts*chunks groups M≤addr) (b : addr<out ∨ out+hosts*chunks groups M≤addr) :
    imageBank hosts groups M out B (image mid (hosts*chunks groups M) (gatherFields tables «fields») mem) addr=mem addr :=
  (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ b).trans (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ a)

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
