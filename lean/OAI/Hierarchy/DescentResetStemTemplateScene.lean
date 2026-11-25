import OAI.Hierarchy.DescentResetStemMaskedPorts
import OAI.Hierarchy.DescentResetStemShapeTemplate
import OAI.Hierarchy.DescentResetStemTicketBook
import OAI.Hierarchy.DescentResetStemLiveDescriptor
import OAI.Hierarchy.DescentOrdinaryMetaRAM

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
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "height" => GroupStage.depthBound D n f g

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

def stemTemplates (j : Fin (2*K)) : Option (Fin (pool).card×Fin (pool).card) :=
  localTemplate (Z).graph shapeBits height (polarity K j) (finProdFinEquiv.symm j).2.val

theorem stemTemplates_at (s : Bool) (j : Fin K) :
    stemTemplates B (headIndex s j)=localTemplate (Z).graph shapeBits height s j.val := by
  simp only [stemTemplates,polarity,headIndex,Equiv.symm_apply_apply,Equiv.apply_symm_apply]

variable {HP prev : ℕ}
/-- The same two-sided template supplies the raw neighbor-evidence program and
the measured compact descriptor publisher. The signed bit is the outer index. -/
theorem stemTemplates_eq (tab : Bool→Fin K→Option (Fin (pool).card×Fin (pool).card))
    (truth : ∀s i,tab s i=localTemplate (Z).graph shapeBits height s i.val) :
    (fun j : Fin (2*K)=>tab (finTwoEquiv (finProdFinEquiv.symm j : Fin 2×Fin K).1)
      (finProdFinEquiv.symm j).2)=stemTemplates B :=by
  funext j
  exact truth _ _

local notation "paletteSize" B₀:arg D₀:arg n₀:arg f₀:arg g₀:arg =>
  (DescentDenseHostOrder.roster (B₀).reset.graph ((B₀).reset.k-(B₀).terminals.commonDepth)
    (GroupStage.depthBound D₀ n₀ f₀ g₀)).card
variable (here : Fin (Fintype.card B.next.V)→Fin (prev*(paletteSize B D n f g))) (parent : Fin (Fintype.card B.next.V)→Fin prev)
  (physical : 0<HP→0< prev*(paletteSize B D n f g)) (near : Fin (prev*(paletteSize B D n f g))→Fin 3→Option (Fin (prev*(paletteSize B D n f g))))
  (hub : Fin prev→Bool)
local notation "scene" => DescentResetStemMaskedPorts.scene (count:=rows) (oldH:=prev) (palette:=(pool).card) (H:=HP) («K»:=2*K) here parent physical near hub (stemTemplates B)

/-- The signed table itself is fixed. Coordinates from the native parent directory
supply the earlier vertex, and the three measured neighbors give the source classes. -/
theorem stemTemplate_active (u : Host) (index : Fin HP) (active : index.val< rows)
    (id : (here ⟨index.val,active⟩).val=(rank u.1.2).val)
    (root : (parent ⟨index.val,active⟩).val=((vertexCode) (center u).1).val)
    (halo : (DescentSortedRoster.present near (here ⟨index.val,active⟩)).map Fin.valEmbedding=stemNeighbors B u)
    (oldHub : hub (parent ⟨index.val,active⟩)=(A).hub (actor u)) (s : Bool) (j : Fin K) :
    metaAt («K»:=K) (H:=HP) (pitch:=prev*(pool).card) (scene) s j index=stemBook B u s j := by
  have nonempty : 0< (pool).card:=((Z).hostFields T (vertexCode) u.1.2).2.pos
  have candidates:=localTemplate_read (Z) T (vertexCode) (center u).1 s j.val nonempty
  unfold metaAt stemBook stemTable
  simp only [DescentResetStemMaskedPorts.scene,DescentResetStemMaskedPorts.chooseRow,
    dite_eq_left active,stemTemplates_at,Scene.neighbors,DescentResetStemTemplatePorts.pack,
    Option.bind_some,Option.map_map,Function.comp_def,finProdFinEquiv_apply_val,Nat.mul_comm,root] at *
  rw [id,halo,oldHub]
  apply congrArg (stemWord _ _ _ _)
  simpa only [Nat.mul_comm] using candidates

theorem stemTemplate_ghost (index : Fin HP) (idle : rows≤ index.val) (s : Bool) (j : Fin K) :
    metaAt («K»:=K) (H:=HP) (pitch:=prev*(pool).card) (scene) s j index=.blank := by
  unfold metaAt
  rw [DescentResetStemMaskedPorts.ends_ghost _ _ _ _ _ _ _ _ idle]
  rfl

theorem chosenStemWord {a : ℕ} (b : ℕ) (u : Host) (s : Bool) (slot : Slot) (key : Cell a)
    (observed : key.val=DescentResetStemKey.code ((oldStemAt B u s slot).map (stemTicket B s))) :
    DescentResetStemMux.pick key (fun j=>DescentResetFieldAssembler.raw b (stemBook B u s j))=
      DescentResetFieldAssembler.raw b («meta» B u (localOrigin B u (stemIndex B s slot))) := by
  rw [←stem_book_read B u s slot,←observed]
  by_cases good : 0< key.val ∧ key.val≤K
  · simp only [DescentResetStemMux.pick,stemBookRead,dite_eq_left good]
  · simp only [DescentResetStemMux.pick,stemBookRead,dite_eq_right good,DescentOrdinarySignedMeta.raw_empty]

/-- Pointwise law used directly under the packed-row encoder. The predecessor key
is consulted only for rows below the measured dense count. -/
theorem nativeStem_word {a : ℕ} (b : ℕ) (index : Fin HP) (g₀ : Fin groups) (x : Fin (2^k))
    (rack : Fin HP→Option B.next.V) (s : Bool) (slot : Slot) (key : Cell a)
    (located : ∀v,rack index=some v→index.val< rows)
    (idle : rack index=none → rows≤ index.val)
    (id : ∀v,(h : rack index=some v)→(here ⟨index.val,located v h⟩).val=(rank v).val)
    (root : ∀v,(h : rack index=some v)→(parent ⟨index.val,located v h⟩).val=
      ((vertexCode) (center ((g₀,v),x)).1).val)
    (halo : ∀v,(h : rack index=some v)→(DescentSortedRoster.present near (here ⟨index.val,located v h⟩)).map
      Fin.valEmbedding=stemNeighbors B ((g₀,v),x))
    (oldHub : ∀v,(h : rack index=some v)→hub (parent ⟨index.val,located v h⟩)=(A).hub (actor ((g₀,v),x)))
    (observed : ∀v,rack index=some v→key.val=DescentResetStemKey.code
      ((oldStemAt B ((g₀,v),x) s slot).map (stemTicket B s))) :
    DescentResetStemMux.pick key (fun j=>DescentResetFieldAssembler.raw b (metaAt («K»:=K) (H:=HP) (pitch:=prev*(pool).card) (scene) s j index)) =
      (rack index).elim 0 (fun v=>DescentResetFieldAssembler.raw b («meta» B ((g₀,v),x) (localOrigin B ((g₀,v),x) (stemIndex B s slot)))) := by
  cases loc : rack index with
  | none=>
    have blank (j : Fin K):=stemTemplate_ghost B here parent physical near hub index (idle loc) s j
    simp only [Option.elim_none,blank,DescentOrdinarySignedMeta.raw_empty]
    unfold DescentResetStemMux.pick
    split <;> rfl
  | some v=>
    have active (j : Fin K):=stemTemplate_active B here parent physical near hub ((g₀,v),x) index
      (located v loc) (id v loc) (root v loc) (halo v loc) (oldHub v loc) s j
    simp only [Option.elim_some,active]
    exact chosenStemWord B b ((g₀,v),x) s slot key (observed v loc)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
