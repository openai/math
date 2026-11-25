import OAI.Computability.BorderVNP.DiagonalTallyReturningRange
import OAI.Computability.BorderVNP.DiagonalNativeTallyClock

/-! # Extracting the local sum bound from the aligned tally evaluator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM DiagonalTallyScatter DiagonalTallyMaterialize
open private supplied_ptr_bound from OAI.Computability.BorderVNP.DiagonalTallyRAMEvaluation
open private supplied_fits from OAI.Computability.BorderVNP.DiagonalTallyMaterializeLoop
open private supplied_unchanged from OAI.Computability.BorderVNP.DiagonalTallyRAMAllocatedRun
open private resident_congr from OAI.Computability.BorderVNP.DiagonalTallyRAMLayout
open private recordsAt_congr from OAI.Computability.BorderVNP.DiagonalTallyScatterLoop
open private seq_tail from OAI.Computability.BorderVNP.DiagonalTallyRAMAcceptance

/-- The actual operand descriptors and the genuine returning bytecode imply the
natural sum bound at every local coordinate. The supplied common claims and the
values of the verified polynomial are immaterial for this implication. -/
theorem Arena.guards_of_evaluate {w : ℕ} (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (os : List Operand) (p : ℕ)
    (fit : a.Fits w (pub 0).val) (resident : a.frame.resident pub m) (ptr : (m ((pub 0).val+44)).val=p)
    (source : supplied m a.fresh p os) (count : os.length=a.count) {es t mt}
    (run : Runs pub mac evaluateTallies s m es t mt) :
    (∀ o ∈ os, o.pair.1<a.dim) ∧ ∀ c<a.dim, a.localRow os c<2^w := by
  have room : a.fresh+2*a.count<2^w := fit.frameFit.2.2.1
  have lo := fit.dir
  have pi : p<2^w := ptr ▸ (m ((pub 0).val+44)).isLt
  have frame : frameAt pub m p a.fresh os.length := ⟨ptr,resident.2.2.1,resident.2.2.2.1.trans count.symm⟩
  obtain ⟨_,v,material,_,_,_⟩ := materialize_runs pub mac s m os p a.fresh a.fresh frame source le_rfl
    (by omega) (supplied_ptr_bound m _ _ os source pi (by omega)) (count ▸ room)
  have stored := resident_congr a.frame pub m (storeAll m a.fresh os) resident
    (fun j _ hj => storeAll_before m a.fresh j os (by omega))
  obtain ⟨_,u,clearRun,_⟩ := clear_runs pub mac v (storeAll m a.fresh os) a.frame stored fit.frameFit
  let initial := a.initialized m os
  have init := resident_congr a.frame pub m initial resident (fun j _ hj => a.initialized_before m os j (by omega))
  obtain ⟨_,rest⟩ := seq_tail (material.seq clearRun) (by decide) run
  obtain ⟨_,_,_,_,_,stages,_⟩ := Runs.seq_iff.mp rest
  obtain ⟨_,z,setup,_,loaded⟩ := scatterSetup_runs pub mac initial u a.frame init fit.frameFit
  obtain ⟨_,other⟩ := seq_tail setup (by decide) stages
  obtain ⟨_,_,_,_,_,scatter,_⟩ := Runs.seq_iff.mp other
  have physical := storeAll_recordsAt m a.fresh os (supplied_fits m _ p os source)
  have recs : RecordsAt initial a.fresh (os.map Operand.pair) := recordsAt_congr _ initial _ _ physical (by
    intro j _ hj
    simp only [List.length_map,count] at hj
    have before : j<a.frame.localBase := hj
    simp [initial,Arena.initialized,cleared,Nat.not_le_of_lt before])
  obtain ⟨coords,accepted⟩ := scatter_return_guards (os.map Operand.pair) loaded
    (by simp only [List.length_map,count,Arena.frame]) (fun i _ => Or.inr (Nat.le_add_right _ i)) recs scatter
  refine ⟨fun o mem => coords o.pair (List.mem_map.mpr ⟨o,mem,rfl⟩),?_⟩
  intro c _
  exact (Nat.le_add_left _ _).trans_lt (accepted (a.frame.localBase+c))

/-- On the aligned post-operand state, the actual guard supplies every local
counter bound without any information about the other teams' private choices. -/
theorem Arena.guards_of_aligned {w : ℕ} (a : Arena) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (os : List Operand) (p : ℕ)
    (seed : a.alignedSeed pub m p) (fit : a.Fits w (pub 0).val) (frame : (pub 0).val+101<2^w)
    (ops : supplied m a.fresh p os)
    (sep : ∀ j, operandReads p os j → outsidePointers (pub 0).val j ∧ j≠(pub 0).val+34)
    (count : os.length=a.count) {es t mt}
    (run : Runs pub mac alignedAllocateAndEvaluate s m es t mt) :
    (∀ o ∈ os, o.pair.1<a.dim) ∧ ∀ c<a.dim, a.localRow os c<2^w := by
  obtain ⟨_,u,mu,align,_,image,_⟩ := alignTallies_runs pub mac s m _ _ seed.2.1 seed.2.2.1
    (by omega) (Nat.le_add_left _ _)
  change readings mu=Function.update (readings m) ((pub 0).val+34) (a.fresh+2*a.count-2*a.count) at image
  rw [Nat.add_sub_cancel] at image
  obtain ⟨_,rest⟩ := seq_tail align (by decide) run
  obtain ⟨_,q,mq,alloc,_,written,dir,_,ptr⟩ := allocateTallies_runs a pub mac u mu p
    (a.seed_after_align pub m mu p seed image) fit frame
  obtain ⟨_,ev⟩ := seq_tail alloc (by decide) rest
  refine a.guards_of_evaluate pub mac q mq os p fit dir ptr ?_ count ev
  apply supplied_unchanged m mq p a.fresh os ops
  intro j hj
  have away := sep j hj
  apply Fin.ext
  change readings mq j=readings m j
  rw [written,a.installed_outside _ _ _ _ away.1,image,Function.update_of_ne away.2]

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
