import OAI.Hierarchy.DescentResetWindowResidentSources
import OAI.Hierarchy.DescentPeerRankFits
import OAI.Hierarchy.DescentRecipeClosedReset
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Four shared native comparisons for the source class of a reset cable -/
namespace Hierarchy.DescentResetSourceClassRAM
open DescentFallbackRankRAM DescentFallbackLeafScan DescentSortedRoster DescentPackedColony ProtocolRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {w at_ : ℕ}

/-- Receivers can reserve one word per candidate source HOST.  The group and
block are unchanged across neighbors and add no whole-word work to this pass.
The sentinel equals the pitch. Repeated neighbors are eliminated by the code. -/
theorem issue {pitch rows : ℕ} (peer : Fin pitch→Fin 4→Option (Fin pitch)) (src : Fin 4→Expr)
    (query : Expr) (out : Bank) (mem : Memory w) (whereAt targetAt : Fin rows→Fin pitch)
    (small : pitch<2^w) (_wide : 4<2^w) (fits : ∀j,(src j).Fits w out.base)
    (qFit : query.Fits w out.base) (space : out.base+rows<2^w)
    (read : ∀r : Fin rows,∀i,(src i).eval mem (r.val:Word w)=(target (peer (whereAt r) i):Word w))
    (wanted : ∀r : Fin rows,(query.eval mem (r.val:Word w)).val=(targetAt r).val) :
    let op:=calculate src query
    let done:=image out.base rows op mem
    let code:=scan w out.base rows op
    code.Exec mem done (4+rows*(2*op.work+4)) ∧
      (∀r : Fin rows,done (out.base+r.val)=(before peer (whereAt r) (targetAt r):Word w)) ∧
      (∀x,x<out.base ∨ out.base+rows≤x→done x=mem x) ∧
      DescentStaticWordColumn.names code=11+4*op.work ∧ CheapCode code := by
  intro op done code
  refine ⟨scan_exec _ _ _ _ (rank_fits src query fits qFit) space,?_,?_,DescentStaticWordColumn.names_scan ..,@scan_cheap _ _ _ _⟩
  · intro r
    exact (ProtocolRAMGeneratedWrite.read_image out.base rows op mem r).trans
      (rank_read peer mem (r.val:Word w) src (whereAt r) small (read r) query (targetAt r) (wanted r))
  · intro x away
    exact ProtocolRAMGeneratedWrite.frame_image out.base rows op mem x away

/-- The shared integer read by this CPU is precisely the ordinal of the
source against a receiver's self-plus-neighbor roster, for any holes and
duplicates in the four original rows. -/
theorem local_class {V : Type} [Fintype V] [DecidableEq V] {pitch : ℕ}
    (name : V↪Fin pitch) (ns : Finset V) (source : V) (rows : Fin pitch→Fin 4→Option (Fin pitch)) (receiver : Fin pitch)
    (roster : present rows receiver=ns.map name) :
    before rows receiver (name source)=(ns.filter (fun v=>name v<name source)).card := by
  unfold before
  rw [roster,←Finset.card_map name (s:=ns.filter (fun v=>name v<name source))]
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_map]
  constructor
  · rintro ⟨⟨v,hv,rfl⟩,lt⟩
    exact ⟨v,⟨hv,lt⟩,rfl⟩
  · rintro ⟨v,⟨hv,lt⟩,rfl⟩
    exact ⟨⟨v,hv,rfl⟩,lt⟩

end
end Hierarchy.DescentResetSourceClassRAM

end OAI
