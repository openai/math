import OAI.Hierarchy.DescentCalendarPeerRegisters
import OAI.Hierarchy.DescentPeerApertureFourWords
import OAI.Hierarchy.DescentPhysicalResetJointScene
import OAI.Hierarchy.DescentPhysicalResetTrunkCensusRead

namespace OAI
/-! # Original sparse peer, compact inverse and old roster on the attained date -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentResetPeerJointRAM DescentResetPeerUnionRAM DescentSortedRoster DescentPackedColony ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable (v : ResetOutput) (base : ℕ) (old : v.OriginalOperands base)
local notation "p₀" => v.front.peer
local notation "cut" => v.actorEnd base
local notation "s₀" => v.issuedScene base old
local notation "regs₀" => v.jointRegisters base old
variable {w N : ℕ} (room : v.front.SceneRoom cut s₀ w) (m : Memory w)
local notation "dst" => v.front.preScalar cut s₀ room m

/-- All four operands of the native peer/joint scan at the original dates.
The stored three raw slots also give its separate absent-self operand. -/
theorem original_joint_reads (name : Fin N→Fin (p₀).hosts)
    (near : Fin (p₀).hosts→Fin 3→Option (Fin (p₀).hosts))
    (prior : Fin (p₀).oldHosts→Fin (p₀).oldDegree→Option (Fin (p₀).oldHosts))
    (three : ∀(a : Fin (p₀).hosts) (j : Fin 3),dst (((v.initialPeers base).base+j.val*(p₀).hosts+a.val))=(target (near a j):Word w))
    (num : m (regs₀).count.base=(N:Word w)) (inv : ∀(j : Fin N),m ((regs₀).inverse.base+j.val)=((name j).val:Word w))
    (inverseSize : N ≤ (regs₀).inverse.size)
    (oldWords : ∀(a : Fin (p₀).oldHosts) (j : Fin (p₀).oldDegree),m ((regs₀).prior.base+(a.val*(p₀).oldDegree+j.val))=(target (prior a j):Word w))
    (countFit : (regs₀).count.Fits w cut) (inverseFit : (regs₀).inverse.Fits w cut)
    (priorFit : (regs₀).prior.Fits w cut) (priorSize : (p₀).oldHosts*(p₀).oldDegree ≤ (regs₀).prior.size) :
    DescentResetPeerJointRAM.Reads regs₀ N name (indexed (selfPeers near)) prior dst ∧
    ∀(a : Fin (p₀).hosts) (j : Fin 3),dst ((v.initialPeers base).base+j.val*(p₀).hosts+a.val)=(target (near a j):Word w) := by
  have held:=v.front.preScalar_lower cut s₀ room m
  refine ⟨⟨?_,?_,inverseSize,?_,?_⟩,three⟩
  · exact (held _ ((Nat.lt_add_of_pos_right countFit.1).trans_le countFit.2.2)).trans num
  · intro j
    exact (held _ ((Nat.add_lt_add_left (j.isLt.trans_le inverseSize) _).trans_le inverseFit.2.2)).trans (inv j)
  · exact (p₀).four_words (s₀).peers (v.front.peers cut) (v.front.prePeers cut s₀ room m) room.peers near three
  · intro a j
    have idx : a.val*(p₀).oldDegree+j.val < (p₀).oldHosts*(p₀).oldDegree :=
      (Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ a.isLt)
    exact (held _ ((Nat.add_lt_add_left (idx.trans_le priorSize) _).trans_le priorFit.2.2)).trans (oldWords a j)

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook DescentCompiler DescentDenseHostOrder DescentResetNewActorDirectory
open DescentSortedRoster DescentSIMDLookup DescentResetPeerUnionRAM DescentPackedColony ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {W : MarkedWorld F d P b}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl) (v : ResetOutput) (base : ℕ) (old : v.OriginalOperands base)
local notation "P₀" => v.front.peer
local notation "H" => (P₀).oldHosts
local notation "cc" => B.terminals.commonDepth
local notation "radius" => B.reset.k-cc
local notation "slots" => (DescentDenseHostOrder.roster B.reset.graph radius (GroupStage.depthBound D n f g)).card
local notation "rawSize" => H*slots
local notation "used" => Fintype.card B.next.V
local notation "len" => v.actorEnd base
local notation "scene" => v.issuedScene base old
local notation "regs₀" => v.jointRegisters base old
variable {M w : ℕ} (pad : Fintype.card input.V ≤ H) (directory : ℕ) (src : Bank) (before : Memory w)
local notation "dir" => (⟨directory,H,slots,chunks (2^cc) M⟩ : DescentResetNewActorDirectory.Layout)
local notation "initial" => (dir).result src before
local notation "previous" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "rank₀" => (previous).trans (Fin.castLEEmb pad)
local notation "name₀" => B.reset.rawHostRank B.terminals rank₀
variable (sizes : (P₀).hosts=rawSize)
local notation "name" => fun j=>(compactActorName B pad j).cast sizes.symm

/-- The compact inverse comes from the preceding actor prefix/inversion on the
original shape-major bits. The prior directory and its ghost sentinel are kept
through that very same run. -/
theorem issued_joint_registers (grid : v.actor.directory (v.middle.stop base)=dir)
    (room : v.front.SceneRoom len scene w)
    (oldPos : 0 < M) (oldBits : M ≤ w)
    (actor : ∀(l : Fin slots) (p : Row H (2^cc) M),before (src.base+l.val*(H*chunks (2^cc) M)+(row H (2^cc) M p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B pad) l) p).val:Word w))
    (sourceFit : src.Fits w directory) (space : rawSize*chunks (2^cc) M ≤ src.size)
    (chunksWide : chunks (2^cc) M ≤ 2^w) (endRoom : (dir).endAddress < 2^w)
    (prior : Fin H→Fin (P₀).oldDegree→Option (Fin H))
    (oldFit : old.oldRoster.Fits w directory) (oldSpan : H*(P₀).oldDegree ≤ old.oldRoster.size)
    (oldRead : ∀(a : Fin H) (j : Fin (P₀).oldDegree),before (old.oldRoster.base+(a.val*(P₀).oldDegree+j.val))=(target (prior a j):Word w))
    (found : Fin rawSize→Fin 3→Option (Fin rawSize))
    (live : ∀(a : Fin rawSize) (j : Fin 3),v.front.preScalar len scene room initial
      ((v.initialPeers base).base+j.val*rawSize+a.val)=(target (found a j):Word w)) :
    let ns:=fun (h : Fin (P₀).hosts) j=>(found (h.cast sizes) j).map (Fin.cast sizes.symm)
    DescentResetPeerJointRAM.Reads regs₀ used name (indexed (selfPeers ns)) prior
        (v.front.preScalar len scene room initial) ∧
      ∀(a : Fin (P₀).hosts) (j : Fin 3),v.front.preScalar len scene room initial
        ((v.initialPeers base).base+j.val*(P₀).hosts+a.val)=(target (ns a j):Word w) := by
  intro ns
  have cutEq : len=(dir).endAddress:=congrArg DescentResetNewActorDirectory.Layout.endAddress grid
  have ct : (regs₀).count=(dir).count:=congrArg DescentResetNewActorDirectory.Layout.count grid
  have inv : (regs₀).inverse=(dir).inverse:=congrArg DescentResetNewActorDirectory.Layout.inverse grid
  obtain ⟨_,count,entries,_,_,frame⟩:=paid_actor_result B pad directory src before oldPos oldBits actor
    sourceFit space chunksWide endRoom
  have actualSize : used ≤ rawSize := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding (α := B.next.V) (β := Fin rawSize) name₀
  have invSize : used ≤ (dir).inverse.size:=actualSize.trans (dir).ordered.1
  have places := (dir).fits endRoom
  have cut₀ : directory ≤ len := by rw [cutEq]; exact Nat.le_add_right ..
  apply v.original_joint_reads base old room initial name ns prior
  · intro a j
    have row:=live (a.cast sizes) j
    cases edge: found (a.cast sizes) j with
    | none=>simpa only [ns,edge,Option.map_none,target,Option.elim_none,Fin.val_cast,sizes] using row
    | some b=>simpa only [ns,edge,Option.map_some,target,Option.elim_some,Fin.val_cast,sizes] using row
  · rw [ct];exact count
  · intro j
    have data:=entries ((compactActorOrder B pad).symm j)
    change initial ((dir).inverse.base+((compactActorOrder B pad) ((compactActorOrder B pad).symm j)).val)=
      ((name₀ ((compactActorOrder B pad).symm j)).val:Word w) at data
    simpa only [inv,Fin.val_cast,compactActorName,Equiv.apply_symm_apply] using data
  · rwa [inv]
  · intro a j
    have point : a.val*(P₀).oldDegree+j.val < H*(P₀).oldDegree :=
      (Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ a.isLt)
    exact (frame _ (.inl ((Nat.add_lt_add_left (point.trans_le oldSpan) _).trans_le oldFit.2.2))).trans (oldRead a j)
  · rw [ct,cutEq];exact places.2.2.2.1
  · rw [inv,cutEq];exact places.2.2.2.2
  · exact ⟨oldFit.1,oldFit.2.1,oldFit.2.2.trans cut₀⟩
  · exact oldSpan

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
