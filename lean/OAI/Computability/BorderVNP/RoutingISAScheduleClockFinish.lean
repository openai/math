import OAI.Computability.BorderVNP.RoutingISAScheduleClockWindows
import OAI.Computability.BorderVNP.CubePhysicalAlignedClaims
import OAI.Computability.BorderVNP.DiagonalTallyCubeOperands

/-! # The post-call window on an actual returning signed trace

The tally of one team can return on a noncanonical global guess. The
trace bound uses only this team's checked row, obtained by inverting its
own run. This gives the same uniform finish window prior to proving global
agreement of the common fields.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM DiagonalTallyRAM DiagonalTallyMaterialize DiagonalTallyCellReports
open BorderVNP.Cube BorderVNP.Cube.Tally

variable {w n b h K s : ℕ}

/-- Physical inputs to the selected-ID writer at the actual private-call return. -/
structure IDInputs (pub : Arg → Word w) (m : Memory w) (id : TableEntry n b h K s → ℕ)
    (f : DiagonalTallyPacketEmit.Frame) (v : Fin f.count → DiagonalTallyPacketEmit.Visit n b h K s)
    (table dst : ℕ) : Prop where
  resident : f.resident (readings pub) (readings m)
  fit : f.Fits (readings m) w (pub 0).val
  recipe : f.recipeAt (readings m) n b h K s
  triples : ∀ i, (v i).tripleAt (readings m) (f.triples+3*i.val)
  banks : ∀ i, VertexAt m (v i).base (v i).selector (v i).vertex (v i).ends (v i).supply
  zero : (m f.zeroAddr).val=0
  one : (m f.oneAddr).val=1
  below : ∀ i, ∀ r ∈ Cube.Tally.recipe (v i).selector (v i).vertex b s,
    r.address (v i).base f.zeroAddr f.oneAddr < f.descriptors
  tableWord : (m ((pub 0).val+47)).val=table
  dstWord : (m ((pub 0).val+71)).val=dst
  deck : ∀ k < 2^argumentWidth n b h K s,
    (m (table+k)).val=idTable (selectorOrder n K h) (vertexOrder _) id k
  tableRoom : table+2^argumentWidth n b h K s ≤ f.descriptors
  apart : f.refs+f.count*f.width ≤ dst
  dstRoom : dst+f.count < 2^w

private theorem aligned_cost (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    {s m es t mt} (os : List Operand) (xs : List (List Bool)) (p : ℕ)
    (ready : AlignedAllocationInput a pub m os xs p) (run : Runs pub mac alignedAllocateAndEvaluate s m es t mt) :
    traceCost es ≤ alignTallies.slots+allocateTallies.slots+a.work w os := by
  have matchRow := alignedAllocateAndEvaluate_sound a pub mac s m os xs p ready run
  obtain ⟨e₀,r₀,m₀,align,c₀,image,_⟩ := alignTallies_runs pub mac s m _ _ ready.seed.2.1 ready.seed.2.2.1
    (by have := ready.frameFit; omega) (Nat.le_add_left _ _)
  change readings m₀ = Function.update (readings m) ((pub 0).val+34) (a.fresh+2*a.count-2*a.count) at image
  rw [Nat.add_sub_cancel] at image
  have input := ready.after_align image
  obtain ⟨e₁,r₁,m₁,alloc,c₁,mem,dir,frame,ptr⟩ := allocateTallies_runs a pub mac r₀ m₀ p input.seed input.fit input.frameFit
  have source := a.source_after_allocation pub m₀ m₁ os xs p input.fit mem dir frame ptr input.operands input.operandsDisjoint
    input.broadcastDisjoint input.count input.coords input.sums input.raw input.number input.lengths
  obtain ⟨e₂,r₂,m₂,ev,c₂,_,_⟩ := evaluateTallies_runs a pub mac r₁ m₁ os xs p source matchRow
  have assembled : Runs pub mac alignedAllocateAndEvaluate s m (e₀++(e₁++e₂)) r₂ m₂ := align.seq (alloc.seq ev)
  obtain ⟨eq,_,_⟩ := run.unique_of_deterministic (by decide) assembled
  rw [eq]
  simp only [traceCost,VPVNP.RAMBuckets.cost_append] at c₀ c₁ c₂ ⊢
  omega

/-- The ID lookup, cube suffix and aligned tallies incur the explicit
post-call allowance. The source following the suffix is the real native
memory image. No cost or successful global row equality is assumed. -/
theorem finish_traceCost (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (id : TableEntry n b h K s → ℕ) (f : DiagonalTallyPacketEmit.Frame)
    (visits : Fin f.count → DiagonalTallyPacketEmit.Visit n b h K s) (table dst demand : ℕ)
    (a : Arena) {l : ReportLayout} (cells : List (ReportCell l)) (q : ReportCursor)
    (sf : DiagonalTallyCubeSuffix.Frame) (same : sf.count=f.count)
    (trueAddr : ℕ) (ids : Fin sf.count → ℕ) (xs : List (List Bool)) (ptr pubWords powers : ℕ)
    (countFields : cells.length*(l.gadgets+l.gadgets*l.countWidth) ≤ pubWords) (use : teamWeighted cells ≤ powers)
    (s₀ : Bank w) (m : Memory w) (load : IDInputs pub m id f visits table dst)
    (suffix : ∀ mu : Memory w, (∀ i : Fin f.count,(mu (dst+i.val)).val=id ((visits i).entry demand)) →
      (∀ j,j<f.descriptors ∨ dst+f.count≤j → mu j=m j) → sf.resident (pub 0).val (readings mu))
    (dirRoom : (pub 0).val+95<2^w) (rowRoom : sf.start+5*sf.count<2^w) (idRoom : sf.ids+sf.count<2^w)
    (ready : ∀ mu mv : Memory w, (∀ i : Fin f.count,(mu (dst+i.val)).val=id ((visits i).entry demand)) →
      (∀ j,j<f.descriptors ∨ dst+f.count≤j → mu j=m j) →
      readings mv=sf.image (pub 0).val (readings mu) →
      AlignedAllocationInput a pub mv (cellOperands cells q++sf.packetOperands (pub 0).val trueAddr ids) xs ptr)
    {es t mt} (run : Runs pub mac (finishExpansion signedOccurrences) s₀ m es t mt) :
    traceCost es ≤ packetIDTicks f.count f.width+
      (64*(pubWords+powers+f.count)+512*(a.teams+1)*(a.dim+1)*(w+1)) := by
  obtain ⟨_,_,es₀,es₁,rfl,rOcc,rComp⟩ := Runs.seq_iff.mp run
  obtain ⟨u,mu,ei,er,rfl,rID,rNext⟩ := Runs.seq_iff.mp rOcc
  obtain ⟨v,mv,esf,ea,rfl,rSuffix,rAlign⟩ := Runs.seq_iff.mp rNext
  obtain ⟨ys,uy,my,found,bid,values,keep,_⟩ := DiagonalTallyPacketEmit.producePacketIDs_runs_separated pub mac s₀ m
    f visits id table dst demand load.resident load.fit load.recipe load.triples load.banks load.zero load.one
    load.below load.tableWord load.dstWord load.deck load.tableRoom load.apart load.dstRoom
  obtain ⟨he,hu,hm⟩ := found.unique_of_deterministic (by decide) rID
  subst ys
  subst uy
  subst my
  obtain ⟨zs,vz,mz,store,bsuf,image,_⟩ := DiagonalTallyCubeSuffix.appendCubeOperands_runs sf pub mac u mu
    (suffix mu values keep) dirRoom rowRoom idRoom
  obtain ⟨hz,hv,hmem⟩ := store.unique_of_deterministic (by decide) rSuffix
  subst zs
  subst vz
  subst mz
  have source := ready mu mv values keep image
  have joined := alignedAllocateAndEvaluate_iff_finish.mpr (rAlign.seq rComp)
  have ba := aligned_cost a pub mac _ _ ptr source joined
  have sparse := alignedWork_le a cells q sf.count
    (fun i => packetOperand sf.parameters (sf.ids+i.val) sf.zeroAddr ((pub 0).val+82) trueAddr (ids i))
    (fun _ => rfl) pubWords powers w countFields use source.count.symm source.fit.width
  change _ ≤ 64*(pubWords+powers+sf.count)+512*(a.teams+1)*(a.dim+1)*(w+1) at sparse
  have c := ba.trans sparse
  rw [same] at c bsuf
  unfold packetIDTicks
  simp only [traceCost,VPVNP.RAMBuckets.cost_append] at bid bsuf c ⊢
  omega

/-- The explicit native finish charge is at most its length-only phase
allowance when the reported vertex count comes from the owned row traversal. -/
theorem finish_window {n b h K s width pubWords powers vertices units teams dim w : ℕ}
    (positive : 1 ≤ units)
    (visited : vertices ≤ TeamRowClock.physicalCoefficient n b h K s*units) :
    packetIDTicks vertices width+(64*(pubWords+powers+vertices)+512*(teams+1)*(dim+1)*(w+1)) ≤
      cubeCoefficient n b h K s width*units+
        64*(pubWords+powers+TeamRowClock.physicalCoefficient n b h K s*units)+512*(teams+1)*(dim+1)*(w+1) := by
  have q := packetID_window n b h K s width vertices units positive visited
  omega

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
