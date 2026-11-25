import OAI.Hierarchy.DescentResetOriginHaloRAM
import OAI.Hierarchy.DescentResetParentOriginHosts
import OAI.Hierarchy.DescentIssuedHostRoster

namespace OAI
/-! # The old host ranking scan reads the same closed halo in both reset charts -/
namespace Hierarchy.DescentResetStemCompactOrder
open DescentSixParty DescentSortedRoster DescentResetOriginHaloRAM DescentGroupPeerOrder
open DescentColonies.DynamicSplit ProtocolRAM DescentPackedColony
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open private Hierarchy.DescentGroupPeerOrder.whole from OAI.Hierarchy.DescentIssuedHostRoster
open scoped Classical Fin.CommRing
noncomputable section
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V]
  {groups d k H w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {g : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W g q ε (Fin groups) V k) (vertex : V↪Fin (Fintype.card V))
  (e : V↪Fin H) (p : Fin H→Fin A.degree→Option (Fin H))
  (same : ∀v,(e v).val=(vertex v).val)
  (assigned : ∀a b,b∈(List.ofFn (p a)).filterMap id ↔ ∃v u:V,a=e v ∧ b=e u ∧ v∈A.near u)

include same assigned in
theorem closed_old_set (v : V) :
    (present (closed p) (e v)).map Fin.valEmbedding=hostDomain A vertex v := by
  rw [present_closed,Hierarchy.DescentGroupPeerOrder.whole A e p assigned]
  ext z
  simp only [hostDomain,Finset.mem_map,Finset.mem_insert,Finset.mem_image,Fin.valEmbedding_apply]
  constructor
  · rintro ⟨u,(rfl|⟨u,hu,rfl⟩),rfl⟩
    · exact ⟨v,Or.inl rfl,(same v).symm⟩
    · exact ⟨u,Or.inr hu,(same u).symm⟩
  · rintro ⟨u,(rfl|hu),rfl⟩
    · exact ⟨e u,Or.inl rfl,same u⟩
    · exact ⟨e u,Or.inr ⟨u,hu,rfl⟩,same u⟩

include same assigned in
theorem measured_halo (v u : V) :
    before (closed p) (e v) (e u)=compress (hostDomain A vertex v) (vertex u).val := by
  rw [←closed_old_set A vertex e p same assigned,←same u]
  simp only [before,compress,Finset.filter_map,Finset.card_map]
  rfl

include same assigned in
theorem halo_rank_column (roster : Bank) (j : Fin (A.degree+1)) (out : ℕ) (m : Memory w)
    (fit : roster.Fits w out) (extent : H*A.degree≤roster.size)
    (original : ∀(v : Fin H) (i : Fin A.degree),m (roster.base+(v.val*A.degree+i.val))=(target (p v i):Word w))
    (high : H<2^w) (degree : A.degree+1<2^w) (output : out+H<2^w) :
    let op:=DescentResetOriginHaloRAM.op H roster j
    let dst:=image out H op m
    (scan w out H op).Exec m dst (4+H*(2*op.work+4)) ∧
    (∀v u : V,(closed p (e v) j).getD (e v)=e u→dst (out+(e v).val)=(compress (hostDomain A vertex v) (vertex u).val:Word w)) ∧
    (∀a,a<out ∨ out+H≤a→dst a=m a) ∧ DescentStaticWordColumn.names (scan w out H op)=11+4*op.work ∧ CheapCode (scan w out H op) := by
  intro op dst
  obtain ⟨exec,seen,frame,num,cheap⟩:=DescentResetOriginHaloRAM.run roster p j out m fit extent original high degree output
  refine ⟨exec,?_,frame,num,cheap⟩
  intro v u atU
  dsimp only [dst,op]
  rw [seen (e v),atU,measured_halo A vertex e p same assigned]

end
end Hierarchy.DescentResetStemCompactOrder

noncomputable section
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase DescentHostDirectory
open DescentResetStemCompactOrder
open scoped Classical
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k

theorem halo_old_set (u : Host) : haloNumbers B u=hostDomain A input.vertex (B.frame.host.symm (receiverRoot B u).1) := by
  ext a
  simp only [haloNumbers,hostDomain,Finset.mem_image]
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨B.frame.host.symm x,?_,(halo_host B x).symm⟩
    rcases Finset.mem_insert.mp hx with rfl|h
    · exact Finset.mem_insert_self ..
    · exact Finset.mem_insert.mpr (.inr ((origin_neighbor B _ _).mp h))
  · rintro ⟨x,hx,rfl⟩
    refine ⟨B.frame.host x,?_,by simpa using halo_host B (B.frame.host x)⟩
    rcases Finset.mem_insert.mp hx with rfl|h
    · exact Finset.mem_insert.mpr (.inl (B.frame.host.apply_symm_apply _))
    · exact Finset.mem_insert.mpr (.inr ((origin_neighbor B _ _).mpr (by simpa using h)))

theorem halo_old_rank (u : Host) (v : B.reset.V) :
    haloNumber B u v=compress (hostDomain A input.vertex (B.frame.host.symm (receiverRoot B u).1))
      (input.vertex (B.frame.host.symm v)).val := by
  rw [haloNumber,halo_old_set,halo_host]
  rfl

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
