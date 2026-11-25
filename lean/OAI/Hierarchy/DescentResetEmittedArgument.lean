import OAI.Hierarchy.DescentClosedResetFreshWires
import OAI.Hierarchy.DescentResetParentWindows
import OAI.Hierarchy.DescentReachedPublicPointer

namespace OAI
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentKernelHistory DescentBundleHistory DescentLocalArchiveOrder DescentCompiler DescentColonies
open DescentResetTrunks DescentRotor DescentResetGates DescentChosenRouter DescentRouterBank
open DescentResetAttachments DescentNamedContact DescentPrimitivePalette Chronology Computability.BorderVNP.Crossing
open DescentStageEdgeReceipt ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist n h C f g cut tail : ℕ} {G : PoweredGadget F}
    {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset cap ctl) (hp : 0<p) (one : 1≤R) (pos : 0<B.reset.unit) (whole : p∣B.reset.unit)
    (wide : max 1 (max B.reset.width (C*B.reset.width))≤R) (a : Archive W) (sh : WorldShape p R a.bit)
local notation "split_" => sh.granular B.count (z*G.b) B.fit hp (B.unit ▸ pos) (B.unit ▸ whole)
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "unit" => B.reset.unit/p
local notation "splitEq" => ((Nat.div_mul_cancel whole).symm : B.reset.unit=unit*p)
local notation "installed" => reentryWorldShape split_ B.reset B.terminals birth _ hp splitEq (resetMenu B) one wide
local notation "after_" => WorldShape.follow hp pos whole B.reblock B.cuts installed
local notation "next_" => (resetArchive B p hp whole a).bit
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "world" => B.reset.orderedOrdinary B.terminals birth
local notation "cnt" => fun e=>(coarse).graph.width e/B.reset.unit
local notation "geo" => B.reset.counts_fit B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans cap.vertex
local notation "dense" => (B.reset.rawHostRank B.terminals vertexCode).trans Fin.valEmbedding
local notation "tape" => B.reset.nativeResetEdges B.terminals vertexCode birth
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw ((tape).order.trans Fin.valEmbedding) S B.valid rawSite
local notation "edgeName" => DescentPhysicalOrder.rename sparse

private theorem reroute_public_read {Tag A A' : Type} {w : A→ℕ} {w' : A'→ℕ} {p : ℕ}
    {r : BitRecipe Tag A w} (s : Shape p r) {route : BitRef w→BitRef w'} (f : BlockMap p w w' route)
    (v : r.Node) (j : ℕ) (b : BlockRef p w) (read : (s.keys v)[j]?=some (.inl b)) :
    ((s.reroute f).keys v)[j]?=some (.inl (f.map b)) := by
  calc
    _ = ((s.keys v).map (Sum.map f.map id))[j]? :=
      congrArg (fun l : List (BlockRef p w' ⊕ BlockRef p r.hiddenWidth) => l[j]?) (reroute_keys s f v)
    _ = ((s.keys v)[j]?).map (Sum.map f.map id) := List.getElem?_map
    _ = _ := by rw [read]; rfl

private theorem split_positive {u p : ℕ} (positive : 0<u) (whole : p∣u) : 0<u/p :=by
  have same:=Nat.div_mul_cancel whole
  by_contra! h
  rw [Nat.eq_zero_of_le_zero h,Nat.zero_mul] at same
  omega

local notation "ht" => split_positive pos whole
local notation "pieces" v:arg => pieceMap (coarse).graph (coarse).core cnt B.reset.unit geo hp ht splitEq v
local notation "rename_" v:arg => namedMap (p:=p) (world) hop edgeName v
local notation "moved" v:arg ref:arg => (rename_ v).map ((pieces ((hop).symm v)).map ref)

/-- The exact pre-split cable, word index and sign determine the installed edge and payload. -/
theorem emitted_reference (v : B.reblock.result.graph.Site) (source : Incident (coarse).graph ((hop).symm v))
    (word : ℕ) (fits : (word+1)*p≤(coarse).graph.width source.val)
    (inside : word/unit<(blocks B).count source.val) (side : Bool)
    (onSide : (if side then (coarse).graph.dst source.val else (coarse).graph.src source.val)=(hop).symm v) :
    let ref : BlockRef p (boundaryWidth (coarse).graph ((hop).symm v)):=⟨.inl source,word,fits⟩
    let out:=moved v ref
    let grain:=(emission B).units ⟨source.val,⟨word/unit,inside⟩⟩
    ∃e : Incident B.reblock.result.graph v,
      out.port=.inl e ∧ out.block=(if source.val∈(coarse).core then word%unit else word) ∧
      grain.1=e.val ∧ (if side then B.reblock.result.graph.dst e.val else B.reblock.result.graph.src e.val)=v :=by
  intro ref out grain
  by_cases marked : source.val∈(coarse).core
  · let u : Fin ((cnt) source.val):=⟨word/unit,by simpa [blocks,weight,marked] using inside⟩
    let e₀ : Incident (world).graph ((hop).symm v):=⟨piece B ⟨source.val,marked⟩ u,source.property⟩
    let e:=PhysicalRename.incident (world).graph hop edgeName v e₀
    have pair:=pieceMap_marked (coarse).graph (coarse).core cnt B.reset.unit geo hp ht splitEq ((hop).symm v)
      source word fits marked u rfl
    refine ⟨e,congrArg (PhysicalRename.boundary (world).graph hop edgeName v) pair.1,?_,?_,?_⟩
    · rw [ite_eq_left marked]
      exact pair.2
    · change (emit B ⟨source.val,⟨word/unit,inside⟩⟩).1=e.val
      simp only [emit, marked, ↓reduceDIte]
      rfl
    · cases side
      · exact (PhysicalRename.src (world).graph hop edgeName e₀.val).trans
          ((congrArg hop onSide).trans ((hop).apply_symm_apply v))
      · exact (PhysicalRename.dst (world).graph hop edgeName e₀.val).trans
          ((congrArg hop onSide).trans ((hop).apply_symm_apply v))
  · let e₀ : Incident (world).graph ((hop).symm v):=⟨.inl ⟨source.val,marked⟩,source.property⟩
    let e:=PhysicalRename.incident (world).graph hop edgeName v e₀
    have pair:=pieceMap_unmarked (coarse).graph (coarse).core cnt B.reset.unit geo hp ht splitEq ((hop).symm v)
      source word fits marked
    refine ⟨e,congrArg (PhysicalRename.boundary (world).graph hop edgeName v) pair.1,?_,?_,?_⟩
    · rw [ite_eq_right marked]
      exact pair.2
    · change (emit B ⟨source.val,⟨word/unit,inside⟩⟩).1=e.val
      simp only [emit, marked, ↓reduceDIte]
      rfl
    · cases side
      · exact (PhysicalRename.src (world).graph hop edgeName e₀.val).trans
          ((congrArg hop onSide).trans ((hop).apply_symm_apply v))
      · exact (PhysicalRename.dst (world).graph hop edgeName e₀.val).trans
          ((congrArg hop onSide).trans ((hop).apply_symm_apply v))

/-- The true flattened slot retains its particular emitted cable through the
reset split and both physical permutations. -/
theorem emitted_argument (rank : Local next_) (pin : P→ℕ) (args : ℕ) (x : NodeOrder.All next_) (j : ℕ)
    (source : Incident (coarse).graph ((hop).symm x.1)) (word : ℕ)
    (fits : (word+1)*p≤(coarse).graph.width source.val) (inside : word/unit<(blocks B).count source.val)
    (read : (((installed).sites ((hop).symm x.1)).keys x.2)[j]?=some (.inl ⟨.inl source,word,fits⟩))
    (side : Bool) (onSide : (if side then (coarse).graph.dst source.val else (coarse).graph.src source.val)=(hop).symm x.1) :
    let grain:=(emission B).units ⟨source.val,⟨word/unit,inside⟩⟩
    let payload:=if source.val∈(coarse).core then word%unit else word
    ∃(e : Incident B.reblock.result.graph x.1) (fit : (payload+1)*p≤B.reblock.result.graph.width e.val),
      grain.1=e.val ∧ (if side then B.reblock.result.graph.dst e.val else B.reblock.result.graph.src e.val)=x.1 ∧
      Reached.argumentPointer B.next next_ rank after_ hp pin args x j=Reached.firstCable B.next hp x.1 e payload fit :=by
  intro grain payload
  let ref : BlockRef p (boundaryWidth (coarse).graph ((hop).symm x.1)):=⟨.inl source,word,fits⟩
  let out:=moved x.1 ref
  have key : (((after_).sites x.1).keys x.2)[j]?=some (.inl out):=by
    let initial := (installed).sites ((hop).symm x.1)
    let splitMap := pieces ((hop).symm x.1)
    let nextMap := rename_ x.1
    have first := reroute_public_read initial splitMap x.2 j ref read
    have second := reroute_public_read (initial.reroute splitMap) nextMap x.2 j _ first
    rw [DescentResetFreshWires.closed_shape B hp one pos whole wide a sh]
    exact second
  have actual:=Reached.argument_public B.next hp pin next_ rank after_ args x.1 x.2 j out key
  obtain ⟨e,port,chunk,issued,orientation⟩:=emitted_reference B hp pos whole x.1 source word fits inside side onSide
  change out.port=.inl e at port
  change out.block=payload at chunk
  have fit : (payload+1)*p≤B.reblock.result.graph.width e.val:=by
    have bounds:=out.fits
    rwa [port,chunk] at bounds
  refine ⟨e,fit,issued,orientation,actual.trans ?_⟩
  generalize hout : out=b at port chunk ⊢
  rcases b with ⟨port₀,offset,ok⟩
  dsimp only at port chunk
  subst port₀
  subst offset
  rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
