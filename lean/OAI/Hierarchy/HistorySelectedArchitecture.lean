import OAI.Hierarchy.HistorySelectedPrograms
import OAI.Hierarchy.HistorySelectedSeedProgram
import OAI.ThreeFlat.RAM.HistoryStageResources

namespace OAI
/-! # Static architecture of the receiver's reached-node loop -/

namespace Hierarchy.HistorySelectedSeed
open ThreeFlat RAM RAM.DescriptorExpr RAM.HistoryInitialSeed
open RAM.HistoryStageBody.Physical Computability.VPVNP.BurstRAM
variable {W : ℕ}

theorem virtual_words_price (A : Layout) (rom : TraceRawLookup.Layout) :
    (words A (liftDecoder (TraceRawLookup.virtual W rom (TraceBucketAtom.publicProgram W)))).binds ≤
      HistorySelectedOps.tariff []+3*rawLeafBinds := by
  have lifted {k : ℕ} (t : Term W k 4) : (liftDecoder t).binds ≤ t.binds := by
    unfold liftDecoder
    simpa only [Nat.mul_one] using
      (HistoryCommandParameter.binds_replace
        (fun i : Fin k => (Term.parameter i.castSucc : Term W (k+1) 0)) t 1
        (by decide) (fun _ => by rfl))
  let dec := TraceRawLookup.virtual W rom (TraceBucketAtom.publicProgram W)
  have raw : dec.binds ≤ 866 * 1000000 :=
    (TraceRawLookup.virtual_binds W rom (TraceBucketAtom.publicProgram W)).trans
      (Nat.mul_le_mul_left 866 (TraceBucketAtom.publicProgram_size W))
  calc
    (words A (liftDecoder dec)).binds ≤ (liftDecoder dec).binds + 128 :=
      words_binds A (liftDecoder dec)
    _ ≤ 866 * 1000000 + 128 := Nat.add_le_add_right ((lifted dec).trans raw) 128
    _ ≤ 3 * rawLeafBinds := by decide
    _ ≤ HistorySelectedOps.tariff [] + 3 * rawLeafBinds := Nat.le_add_left _ _


end Hierarchy.HistorySelectedSeed

namespace Hierarchy.HistorySelectedReceiverLoop
open ThreeFlat RAM RAM.PhysicalProcedure Diagonal.PhysicalStage
open RAM.HistoryStageBody.Physical Computability.VPVNP.BurstRAM
open scoped Classical
open private leafResources_eq from OAI.ThreeFlat.RAM.HistoryStageLeafResources
open private folded_budget from OAI.ThreeFlat.RAM.HistoryStageSelectedResources
open private familiesFrom_schema from OAI.ThreeFlat.RAM.HistoryStageResources
noncomputable section

/-- The virtual leaf includes the actual trace bucket ROM and its public slots. -/
theorem seed_resources {W : ℕ} (A : HistoryInitialSeed.Layout) (rom : TraceRawLookup.Layout)
    (pub : Fin (1+TraceBucketAtom.bankSize)→Word W) :
    resources (HistorySelectedSeed.procedure A
      (TraceRawLookup.virtual W rom (TraceBucketAtom.publicProgram W)) pub)≤leafResources := by
  rw [HistorySelectedSeed.procedure,resources_seq,HistoryInitialSeed.seed,resources_write,
    resources_tape,HeaderScan.binds_closed]
  have seed:=HistoryInitialSeed.seed_budget A
  have row:=HistorySelectedSeed.virtual_words_price (W:=W) A rom
  have slots : 1+TraceBucketAtom.bankSize+1≤TraceEndpointROM.params+1 := by
    unfold TraceEndpointROM.params
    omega
  rw [←leafResources_eq]
  omega

/-- Address changes in a stage family preserve its code bound. Each arm occurs
once in the compiled control flow, even when its loop executes many times. -/
theorem selected_resources_of_leaf {W : ℕ} (u : ℕ) (bank : Archive)
    (leaf : Procedure W) (leafBound : resources leaf≤leafResources)
    (fs gs : List Family) (same : gs.map Family.schema=fs.map Family.schema) :
    resources (selected u bank leaf gs)≤ selectedResources fs := by
  have folded : resources (body u bank leaf gs) ≤
      leafResources + (fs.map (fun f => 6+4*(enabled 0 f).work+armResources f)).sum :=
    folded_budget leaf leafResources leafBound
      (fun g => HistoryStageBody.procedure (layout u bank g) g.childBound W)
      (enabled u) (fun f => (enabled 0 f).work) armResources
      (fun f g => enabled_work u 0 g f) fs
      (fun f _ g eqv => arm_resources f W u bank g eqv) gs same
  calc
    resources (selected u bank leaf gs) = 49 + resources (body u bank leaf gs) :=
      resources_guard (ownerData W u) (body u bank leaf gs)
    _ ≤ 49 + (leafResources + _) := Nat.add_le_add_left folded 49
    _ = _ := (Nat.add_assoc ..).symm

/-- One finite label, register, and public-slot budget works simultaneously at
every word width, every age, every archive placement and every trace layout. -/
theorem block_resources {F : Type} [Field F] [Fintype F] (B : Block F) (start pages W u : ℕ)
    (bank : Archive) (shape : TraceBucketAtom.Layout) (rom : TraceRawLookup.Layout)
    (rest : Fin 1→Word W) :
    let leaf:=HistorySelectedSeed.procedure (initial u shape)
      (TraceRawLookup.virtual W rom (TraceBucketAtom.publicProgram W)) (TraceBucketAtom.publicData shape rest)
    let p:=selected u bank leaf (families B start pages)
    p.labels+p.registers+p.slots≤ selectedResources (families B 0 0) := by
  apply selected_resources_of_leaf
  · exact seed_resources _ _ _
  · apply familiesFrom_schema

end
end Hierarchy.HistorySelectedReceiverLoop

end OAI
