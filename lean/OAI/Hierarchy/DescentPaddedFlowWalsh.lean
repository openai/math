import OAI.Hierarchy.DescentPaddedFlowChips
import OAI.Hierarchy.DescentPackedFlowWalsh

namespace OAI
/-! # Authentic old signed arrays on one public host and port rectangle -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentColonies DescentGL DescentSIMDLookup DescentStageEdgeReceipt DescentPackedColony DescentPackedWalsh
open Computability.VPVNP.BurstRAM
open DescentPackedFlowPair.Padded
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i h l H N R D M short b w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (groups : J≃Fin R) (hosts : V≃Fin H) (ph : H≤N) (pd : A.degree≤D)
local notation "Q" => A.wire*(A.z*G.b)
local notation "coords" => DescentWalshPhysical.coordinates
local notation "rank" => hosts.toEmbedding.trans (Fin.castLEEmb ph)

include pd in
theorem walsh_inputs (L : DescentPackedFlowPublication.Layout D (2^k) (2*A.cap))
    (room : DescentPackedFlowPublication.Room L N R M short b w) (size : 2^(h+l)=R*2^k)
    (lanes : 2^l=M*2^k) (hm : 0<M) (ok : A.degree<2^short) (mem : Memory w)
    (old : ∀s,Reads (L.tokens s) (fun (v : Fin N) g=>tokens A native S ready groups hosts short v g s) M mem)
    (rom : ∀(j : Fin D) x,DescentPackedZip.Static (L.inserts j x)
      (DescentPackedFlowRAM.insert (b:=b) (d:=short) Q j.val x) M mem)
    (links : Mounted L.peers (roster (D:=D) A hosts ph) mem R M)
    (idx : DescentPackedFlowReturn.Header L.header L.middle mem D N R M)
    (table : DescentPackedZip.Static L.add (DescentPackedFlowPair.add (b:=b) (r:=2^k)) M mem) :
    let xy:=digits groups size
    ∃dst : Memory w,(DescentPackedFlowPublication.procedure L N R M w).Exec mem dst
      (DescentPackedFlowPublication.duration L N R M) ∧
      (∀j : Fin D,Installed (L.middle+j.val*L.pitch) (fun (v : Fin N)=>shaped
        (fun z=>(flow A hosts xy j v (address (h+l) ((coords _).symm z)):Cell b))) dst) ∧
      (∀a<L.first,dst a=mem a) ∧ ∀a,L.middle+D*L.pitch≤a→dst a=mem a := by
  intro xy
  obtain ⟨dst,ran,published,low,high⟩:=DescentPackedFlowPublication.run_framed L room Q (roster A hosts ph)
    (tokens A native S ready groups hosts short) mem old rom links idx table
  refine ⟨dst,ran,?_,low,high⟩
  intro j
  apply DescentPackedResetSource.from_grouped size lanes hm (Nat.two_pow_pos _) _ dst
    (fun v x=>(flow A hosts xy j v x:Cell b))
  intro p
  rw [published j p]
  apply congrArg (fun a : Fin N→Fin R→Cell (b*2^k)=>((data a p).val:Word w))
  funext v g
  apply congrArg (encode b (2^k))
  funext x
  apply congrArg (fun u : ℕ=>(u:Cell b))
  let z:=Fin.cast size.symm (finProdFinEquiv (g,x))
  have parts : xy z=(groups.symm g,x):=digits_at groups size g x
  simpa only [parts,Equiv.apply_symm_apply] using measured_amount A native S ready groups hosts ph pd ok xy v j z

include S ready in
theorem census_value (xy : Block (h+l)≃J×Block k) (v : Fin N) (x : Block (h+l)) :
    A.censusValue rank groups false v (groups (xy x).1) (xy x).2=load A hosts xy v x := by
  cases hp:project H v with
  | none=>
    have absent : ¬∃u,rank u=v := by
      rintro ⟨u,hu⟩
      have inside : v.val < H := by
        rw [←hu]
        exact (hosts u).isLt
      simp [project,inside] at hp
    simp only [GroupStage.censusValue,dite_eq_right absent,load,hp,Option.elim_none]
  | some u=>
    have same:=project_some hp ph
    subst v
    have fromCensus:=A.reset_census S ready rank groups xy (hosts.symm u) x
    simpa only [Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.apply_symm_apply,Fin.castLEEmb_apply,
      load,project_cast,Option.elim_some] using fromCensus

include S ready in
theorem walsh_load (size : 2^(h+l)=R*2^k) (lanes : 2^l=M*2^k) (hm : 0<M)
    (base : ℕ) (mem : Memory w) (measured : ∀p : Row N R M,mem (base+(DescentSIMDLookup.row N R M p).val)=
      ((data (fun v g=>encode b (2^k) (fun x=>(A.censusValue rank groups false v g x:Cell b))) p).val:Word w)) :
    let xy:=digits groups size
    Installed base (fun (v : Fin N)=>shaped (fun z=>(load A hosts xy v (address (h+l) ((coords _).symm z)):Cell b))) mem := by
  intro xy
  apply DescentPackedResetSource.from_grouped size lanes hm (Nat.two_pow_pos _) base mem
    (fun (v : Fin N) x=>(load A hosts xy v x:Cell b))
  intro p
  rw [measured p]
  apply congrArg (fun a : Fin N→Fin R→Cell (b*2^k)=>((data a p).val:Word w))
  funext v g
  apply congrArg (encode b (2^k))
  funext x
  apply congrArg (fun z : ℕ=>(z:Cell b))
  let z:=Fin.cast size.symm (finProdFinEquiv (g,x))
  have parts : xy z=(groups.symm g,x):=digits_at groups size g x
  simpa only [parts,Equiv.apply_symm_apply] using census_value A S ready groups hosts ph xy v z

end
end Hierarchy.DescentSixParty.PackedFlow.Padded

end OAI
