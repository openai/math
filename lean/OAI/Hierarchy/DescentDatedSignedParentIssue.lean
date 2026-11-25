import OAI.Hierarchy.DescentDatedSignedInput
import OAI.Hierarchy.DescentDatedMaterialSourceRun
import OAI.Hierarchy.DescentDatedSignedLocalRecords

namespace OAI
/-! Carry all nine physical source sockets to the start of signing, across the later peer and marking scans. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSIMDLookup DescentPackedZip DescentHaloWalkRAM DescentSharedCableNames DescentParallelBase.ParentFilter
open DescentOrdinaryDonorSources DescentRawCablePanel.DepotRAM.Material.Route
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (s : SignedExtent) (I : s.Input) (R : Fin s.priorHosts→Fin s.degree→Option (Fin s.priorHosts))
    (raw : s.Socket→Fin s.hosts→Fin s.groups→Option (Fused.Raw R s.lowSites s.tickets s.cap s.fieldBits))

def donorSocket (z : s.Socket) : Fin 9→Expr :=
  ![I.endpoints z false,I.endpoints z true,I.path z,
    I.donor z 0,I.donor z 1,I.donor z 2,I.donor z 3,I.donor z 4,I.donor z 5]

theorem donors_held {w old new₀ : ℕ} (m after : Memory w)
    (numeric : ∀z f,Source (s.donorSocket I z f) (fun h g=>atPort R (raw z h g) f) s.lanes m)
    (fit : ∀z f,(s.donorSocket I z f).Fits w old)
    (ordered : old≤new₀) (kept : ∀a<old,after a=m a)
    (origin : ∀z h g u,raw z h g=some u→s.rack I.hostPitch h=some u.receiver.1 ∧
      Gather.select (Gather.reaching R) u.receiver.1 u.path=some u.host) :
    s.Donors I R raw new₀ after :=by
  have now (z : s.Socket) (f : Fin 9):Source (s.donorSocket I z f)
      (fun h g=>atPort R (raw z h g) f) s.lanes after:=by
    intro p
    exact (ProtocolRAM.eval_below (s.donorSocket I z f) _ m after (fit z f) kept).trans (numeric z f p)
  have enlarge (e:Expr) (ok:e.Fits w old) : e.Fits w new₀:=by
    induction e <;> simp_all [Expr.Fits,Bank.Fits]; omega
  refine ⟨fun z=>?_,fun z side=>?_,fun z j=>?_,fun z=>enlarge _ (fit z 2),?_,?_,?_,?_⟩
  · simpa [donorSocket,atPort] using now z 2
  · cases side <;> first |simpa [donorSocket,atPort] using now z 0|simpa [donorSocket,atPort] using now z 1
  · fin_cases j <;> first |simpa [donorSocket,atPort] using now z 3|simpa [donorSocket,atPort] using now z 4
                           |simpa [donorSocket,atPort] using now z 5|simpa [donorSocket,atPort] using now z 6
                           |simpa [donorSocket,atPort] using now z 7|simpa [donorSocket,atPort] using now z 8
  · intro z side;cases side <;> first |exact enlarge _ (fit z 0)|exact enlarge _ (fit z 1)
  · intro z j;fin_cases j <;> first |exact enlarge _ (fit z 3)|exact enlarge _ (fit z 4)|exact enlarge _ (fit z 5)
                                    |exact enlarge _ (fit z 6)|exact enlarge _ (fit z 7)|exact enlarge _ (fit z 8)
  · intro z h g u q;exact (origin z h g u q).1
  · intro z h g u q;exact (origin z h g u q).2

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
