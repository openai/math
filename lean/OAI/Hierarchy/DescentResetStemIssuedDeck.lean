import OAI.Hierarchy.DescentResetStemTemplateScene
import OAI.Hierarchy.DescentResetStemProjected
import OAI.Hierarchy.DescentResetStemIssuedWindows

namespace OAI
/-! # The measured public stem template resolves to the physical row emitted at every occupied host -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical
open scoped Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "groups" => S.groupCount (i+1)
local notation "height" => GroupStage.depthBound D n f g

local notation "rawRank" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding

local notation "A" => input.placement
local notation "c" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k

local notation "Slot" => Fin (2^(m-c))×Fin (2*(A).cap)

open DescentResetFieldAssembler DescentResetWindowResidentSources
local notation "rank" => (Z).rawHostRank T vertexCode

local notation "center" => receiverRoot B
local notation "actor" => fun u => B.frame.host.symm (center u).1

open DescentResetStemDecoder DescentRelativeContacts
local notation "Y" => 2^(Z).n
local notation "shapeBits" => (Z).k-c

local notation "shapeCount" => DescentFallbackShapeTable.rows shapeBits Y
local notation "K" => 2*shapeCount

open DescentResetStemPackedIssue DescentResetStemPackedIssue.Mixed
open DescentSIMDLookup DescentResetStemIncidence
local notation "pool" => DescentDenseHostOrder.roster (Z).graph shapeBits height
local notation "rows" => Fintype.card B.next.V

open DescentResetStemPackedIssue.Mixed DescentPackedZip DescentDyadicSpan ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
local notation "L" => 2^(m-c)
local notation "Q" => DescentResetStemPackedIssue.count L (A).cap
local notation "sid" => DescentResetStemPackedIssue.side L (A).cap
local notation "ord" => DescentResetStemPackedIssue.ordinal L (A).cap
local notation "X" => 2^k
local notation "degree" => (A).degree
variable {prev HP f₀ w₀ : ℕ}
variable (base ptr b M₀ M : ℕ) (parse : DescentResetStemKey.Decoder input.placement.degree f₀)
  (src : Fin (DescentResetStemPackedIssue.count
      (2^(S.groupWidth k tail i+k-B.terminals.commonDepth)) input.placement.cap)→Fin (input.placement.degree+2)→Expr) (ports : DescentResetStemIncidence.Ports
      (2*(2*DescentFallbackShapeTable.rows (B.reset.k-B.terminals.commonDepth) (2^B.reset.n))))
local notation "paletteSize" B₀:arg D₀:arg n₀:arg f₀:arg g₀:arg =>
  (DescentDenseHostOrder.roster (B₀).reset.graph ((B₀).reset.k-(B₀).terminals.commonDepth)
    (GroupStage.depthBound D₀ n₀ f₀ g₀)).card
variable (here : Fin (Fintype.card B.next.V)→Fin (prev*(paletteSize B D n f g))) (parent : Fin (Fintype.card B.next.V)→Fin prev)
  (physical : 0<HP→0< prev*(paletteSize B D n f g)) (near : Fin (prev*(paletteSize B D n f g))→Fin 3→Option (Fin (prev*(paletteSize B D n f g))))
  (hub : Fin prev→Bool)
local notation "scene" => DescentResetStemMaskedPorts.scene (count:=rows) (oldH:=prev) (palette:=(pool).card) (H:=HP) («K»:=2*K) here parent physical near hub (stemTemplates B)
local notation "cut" => DescentResetStemPackedIssue.Mixed.Projected.splitAt base Q degree prev groups X f₀ M₀ M
local notation "Aren" => DescentResetStemPackedIssue.Mixed.plan cut ptr K HP
local notation "last" => Projected.image base ptr b prev HP groups X M₀ M parse sid src ports

/-- The signed low slot lies in an x-major packed output bank. The row encoder
gives zero to padding lanes and to every unoccupied dense actor. -/
theorem emitted_stems (initial : Memory w₀) (ha : 0<M₀) (hm : 0<M)
    (old : Fin Q→Fin prev→Fin (groups*X)→Fin (degree+2)→Cell f₀)
    (fit : ∀q i,(src q i).Fits w₀ base) (read : ∀q i,Source (src q i) (fun a g=>old q a g i) M₀ initial)
    (mounted : DescentResetStemIncidence.Reads ports (scene) initial) (safe : ports.All (Expr.Fits w₀ base))
    (owner : Fin HP→Fin prev) (directory : DescentResetStemKeyReindex.Directory ptr owner initial)
    (ptrFit : ptr+span HP≤ base) (hostFit : prev*(pool).card<2^w₀) (width : (b*7)*M≤ w₀)
    (zero : parse 0=none) (limit : Projected.extent base ptr degree f₀ b K prev HP groups X M₀ M Q<2^w₀)
    (rack : Fin HP→Option B.next.V)
    (located : ∀r v,rack r=some v → r.val< rows) (idle : ∀r,rack r=none → rows≤ r.val)
    (id : ∀r v,(h₁ : rack r=some v)→(here ⟨r.val,located r v h₁⟩).val=(rank v).val)
    (root : ∀r v,(h₁ : rack r=some v)→(parent ⟨r.val,located r v h₁⟩).val=
      ((vertexCode) (position (Z).graph v.val)).val)
    (halo : ∀r v,(h₁ : rack r=some v)→(DescentSortedRoster.present near (here ⟨r.val,located r v h₁⟩)).map
      Fin.valEmbedding=(B.next.placement.near v).map rawRank)
    (oldHub : ∀r v,(h₁ : rack r=some v)→hub (parent ⟨r.val,located r v h₁⟩)=(A).hub (B.frame.host.symm (position (Z).graph v.val)))
    (key : ∀s (slot : Slot) r v g₀ x,rack r=some v→
      (DescentResetStemKey.word parse s (old ((ord) (s,slot)) (owner r) (finProdFinEquiv (g₀,x)))).val=
        DescentResetStemKey.code ((oldStemAt B ((g₀,v),x) s slot).map (stemTicket B s))) :
    (Projected.program base ptr b prev HP groups X M₀ M parse sid src ports w₀).Exec initial (last initial)
      (Projected.ticks base ptr b prev HP groups X M₀ M parse sid src ports w₀) ∧
    ∀x s (slot : Slot) (p : Row HP groups M),
      last initial ((Aren).out degree f₀ (b*7) K M prev HP groups (X*Q)+
        (finProdFinEquiv (x,(ord) (s,slot))).val*(HP*chunks groups M)+(row HP groups M p).val)=
        ((data (fun r g₀=>(rack r).elim 0 (fun v=>DescentResetFieldAssembler.raw b («meta» B ((g₀,v),x)
          (localOrigin B ((g₀,v),x) (stemIndex B s slot))))) p).val:Word w₀) := by
  have run_:=Projected.run base ptr b prev HP groups X M₀ M parse sid src ports initial ha hm (Nat.two_pow_pos _) fit old read
    (scene) mounted safe owner directory ptrFit hostFit width zero limit
  refine ⟨run_.1,?_⟩
  intro x s slot p
  have contents:=run_.2.1 x ((ord) (s,slot)) p
  simp only [DescentResetStemPackedIssue.side,Equiv.symm_apply_apply] at contents
  rw [contents]
  apply congrArg (fun z : ℕ=>(z:Word w₀))
  apply congrArg Fin.val
  apply congrArg (fun dataAt=>data dataAt p)
  funext index g₀
  exact nativeStem_word B here parent physical near hub b index g₀ x rack s slot _
    (located index) (idle index) (id index) (root index) (halo index) (oldHub index) (key s slot index · g₀ x)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
