import OAI.Computability.BorderVNP.FiniteEvaluatorCubeReadSet
import OAI.Computability.BorderVNP.TransmissionInverseBit
import OAI.Computability.BorderVNP.RoutingISACallInversion
import OAI.Computability.BorderVNP.RoutingISALoops

/-! # Post-private-call readback of the cube and sparse tally words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellDispatch

open VPVNP.BurstRAM

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

private theorem row_memory {s m es t mt} (run : Runs pub mac body s m es t mt) : mt=m := by
  obtain ⟨u,mu,_,_,_,owner,rest⟩ := Runs.seq_iff.mp run
  obtain ⟨v,mv,_,_,_,test,advance⟩ := Runs.seq_iff.mp rest
  have beginning := owner.memory_eq_of_storeFree (by decide)
  have end_ := advance.memory_eq_of_storeFree (by decide)
  obtain ⟨_,_,branch⟩ := eq_split test
  by_cases own : u 3=u 8
  · rw [ite_eq_left own] at branch
    obtain ⟨_,_,_,_,_,args,privateCall⟩ := Runs.seq_iff.mp branch
    exact end_.trans ((private_iff.mp privateCall).2.2.1.trans ((args.memory_eq_of_storeFree (by decide)).trans beginning))
  · rw [ite_eq_right own] at branch
    exact end_.trans ((branch.memory_eq_of_storeFree (by decide)).trans beginning)

/-- The private routine reads its burst interval. No successful cell dispatch path
writes the shared memory, including when a machine-word cursor happens to wrap. -/
theorem memory_after_owned_calls {s m es t mt} (run : Runs pub mac callOwnedCells s m es t mt) : mt=m := by
  obtain ⟨_,mu,_,_,_,prepare,loop⟩ := Runs.seq_iff.mp run
  have start : mu=m := prepare.memory_eq_of_storeFree (by decide)
  exact (loop.while_invariant 6 5 body (fun _ mm => mm=m)
    (fun held _ row => (row_memory row).trans held) rfl start).1

end RoutingISA.CellDispatch

namespace FiniteEvaluator.CubePacket

open VPVNP.BurstRAM RoutingISA

variable {n b h K s w : ℕ} {F : Type*} {P : Inputs n b h K s F}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {bank t : Bank w} {mem mt : Memory w} {es : List (TeamRAM.Event w)}

/-- The prepared real lookup frame, deck, owned vertex triples and local packet
banks survive all possible private choices and signs of the owned cell calls. -/
theorem Prepared.after_owned_calls [Fintype F] (prepared : Prepared P pub mem)
    (calls : Runs pub mac callOwnedCells bank mem es t mt) : Prepared P pub mt :=
  (CellDispatch.memory_after_owned_calls calls) ▸ prepared

/-- Each read word after the calls retains the value proved by the actual pre-call
prefix, independently of which cell paths returned. -/
theorem readAt_after_owned_calls {orig : Memory w} (reads : ∀ a,ReadAt P pub a → mem a=orig a)
    (calls : Runs pub mac callOwnedCells bank mem es t mt) : ∀ a,ReadAt P pub a → mt a=orig a :=
  (CellDispatch.memory_after_owned_calls calls) ▸ reads

end FiniteEvaluator.CubePacket

end BorderVNP
end Computability
end OAI
