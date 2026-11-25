import OAI.Hierarchy.DescentPackedFlowPublication
import OAI.Hierarchy.DescentPackedFlowStage
import OAI.Hierarchy.DescentPackedResetCensus

namespace OAI
/-! # Native signed old-cable and old-site census sources for the measured Walsh reset -/
namespace Hierarchy.DescentSixParty.PackedFlow
open DescentColonies DescentGL DescentSIMDLookup DescentPackedColony DescentPackedWalsh Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i h l H R M short b w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (groups : J≃Fin R) (hosts : V≃Fin H)
local notation "rs" => groups.toEmbedding.trans Fin.valEmbedding
local notation "vs" => hosts.toEmbedding.trans Fin.valEmbedding
local notation "Q" => A.wire*(A.z*G.b)
local notation "coords" => DescentWalshPhysical.coordinates

/-- Physical group and block coordinates in the previous ordinary census. -/
def digits (size : 2^(h+l)=R*2^k) : Block (h+l)≃J×Block k :=
  ((finCongr size).trans finProdFinEquiv.symm).trans (groups.symm.prodCongr (Equiv.refl _))

omit [Fintype J] [DecidableEq J] in
theorem digits_at (size : 2^(h+l)=R*2^k) (g : Fin R) (x : Block k) :
    digits groups size (Fin.cast size.symm (finProdFinEquiv (g,x)))=(groups.symm g,x) := by simp [digits,finCongr]

theorem walsh_inputs_framed (L : DescentPackedFlowPublication.Layout A.degree (2^k) (2*A.cap))
    (room : DescentPackedFlowPublication.Room L H R M short b w)
    (size : 2^(h+l)=R*2^k) (lanes : 2^l=M*2^k) (hm : 0<M) (ok : A.degree<2^short)
    (mem : Memory w)
    (old : ∀s,Reads (L.tokens s) (fun v g=>chips A native S ready rs vs short (groups.symm g) (hosts.symm v) s) M mem)
    (rom : ∀(j : Fin A.degree) x,DescentPackedZip.Static (L.inserts j x)
      (DescentPackedFlowRAM.insert (b:=b) (d:=short) Q j.val x) M mem)
    (roster : Mounted L.peers (next A hosts) mem R M)
    (idx : DescentPackedFlowReturn.Header L.header L.middle mem A.degree H R M)
    (table : DescentPackedZip.Static L.add (DescentPackedFlowPair.add (b:=b) (r:=2^k)) M mem) :
    let D:=digits groups size
    ∃dst : Memory w,(DescentPackedFlowPublication.procedure L H R M w).Exec mem dst
      (DescentPackedFlowPublication.duration L H R M) ∧
      (∀j : Fin A.degree,Installed (L.middle+j.val*L.pitch) (fun v=>shaped
        (fun z=>(raw A hosts D j v (address (h+l) ((coords _).symm z)):Cell b))) dst) ∧
      (∀a<L.first,dst a=mem a) ∧ ∀a,L.middle+A.degree*L.pitch≤a→dst a=mem a := by
  intro D
  obtain ⟨dst,ran,published,frame,high⟩:=DescentPackedFlowPublication.run_framed L room Q (next A hosts)
    (fun v g=>chips A native S ready rs vs short (groups.symm g) (hosts.symm v)) mem old rom roster idx table
  refine ⟨dst,ran,?_,frame,high⟩
  intro j
  apply DescentPackedResetSource.from_grouped size lanes hm (Nat.two_pow_pos _) _ dst
    (fun v x=>(raw A hosts D j v x:Cell b))
  intro p
  rw [published j p]
  apply congrArg (fun f : Fin H→Fin R→Cell (b*2^k)=>((data f p).val:Word w))
  funext v g
  apply congrArg (encode b (2^k))
  funext x
  apply congrArg (fun n : ℕ=>(n:Cell b))
  let z:=Fin.cast size.symm (finProdFinEquiv (g,x))
  have parts : D z=(groups.symm g,x):=digits_at groups size g x
  change DescentPackedFlowPair.paid (next A hosts) (weights A native S ready groups hosts short)
    v g j x = raw A hosts D j v z
  have recorded := raw_at A native S ready groups hosts short ok D j v z
  rw [parts] at recorded
  simpa only [Equiv.apply_symm_apply] using recorded

theorem walsh_inputs (L : DescentPackedFlowPublication.Layout A.degree (2^k) (2*A.cap))
    (room : DescentPackedFlowPublication.Room L H R M short b w)
    (size : 2^(h+l)=R*2^k) (lanes : 2^l=M*2^k) (hm : 0<M) (ok : A.degree<2^short)
    (mem : Memory w)
    (old : ∀s,Reads (L.tokens s) (fun v g=>chips A native S ready rs vs short (groups.symm g) (hosts.symm v) s) M mem)
    (rom : ∀(j : Fin A.degree) x,DescentPackedZip.Static (L.inserts j x)
      (DescentPackedFlowRAM.insert (b:=b) (d:=short) Q j.val x) M mem)
    (roster : Mounted L.peers (next A hosts) mem R M)
    (idx : DescentPackedFlowReturn.Header L.header L.middle mem A.degree H R M)
    (table : DescentPackedZip.Static L.add (DescentPackedFlowPair.add (b:=b) (r:=2^k)) M mem) :
    let D:=digits groups size
    ∃dst : Memory w,(DescentPackedFlowPublication.procedure L H R M w).Exec mem dst
      (DescentPackedFlowPublication.duration L H R M) ∧
      (∀j : Fin A.degree,Installed (L.middle+j.val*L.pitch) (fun v=>shaped
        (fun z=>(raw A hosts D j v (address (h+l) ((coords _).symm z)):Cell b))) dst) ∧
      ∀a<L.first,dst a=mem a := by
  obtain ⟨dst,run,rows,lo,_⟩:=walsh_inputs_framed A native S ready groups hosts L room size lanes hm ok mem old rom roster idx table
  exact ⟨dst,run,rows,lo⟩

include S ready in
theorem walsh_load (size : 2^(h+l)=R*2^k) (lanes : 2^l=M*2^k) (hm : 0<M) (base : ℕ) (mem : Memory w)
    (issued : ∀p : Row H R M,mem (base+(DescentSIMDLookup.row H R M p).val)=
      ((data (fun v g=>encode b (2^k) (fun x=>(A.censusValue hosts.toEmbedding groups false v g x:Cell b))) p).val:Word w)) :
    let D:=digits groups size
    Installed base (fun v=>shaped (fun z=>(A.resetLoad D (hosts.symm v) (address (h+l) ((coords _).symm z)):Cell b))) mem := by
  intro D
  apply DescentPackedResetSource.from_grouped size lanes hm (Nat.two_pow_pos _) base mem
    (fun v x=>(A.resetLoad D (hosts.symm v) x:Cell b))
  intro p
  rw [issued p]
  apply congrArg (fun f : Fin H→Fin R→Cell (b*2^k)=>((data f p).val:Word w))
  funext v g
  apply congrArg (encode b (2^k))
  funext x
  apply congrArg (fun n : ℕ=>(n:Cell b))
  let z:=Fin.cast size.symm (finProdFinEquiv (g,x))
  have parts : D z=(groups.symm g,x):=digits_at groups size g x
  simpa only [parts,Equiv.apply_symm_apply,Equiv.toEmbedding_apply] using
    A.reset_census S ready hosts.toEmbedding groups D (hosts.symm v) z

end
end Hierarchy.DescentSixParty.PackedFlow

end OAI
