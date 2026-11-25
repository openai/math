import OAI.Hierarchy.DescentDatedDonorNumeral
import OAI.Hierarchy.DescentMeasuredHaloChart
import OAI.Hierarchy.DescentParentLocalRank
import OAI.Hierarchy.DescentOrdinaryRankBanks

namespace OAI
/-! # Selecting the old node's local donor rank from the measured receiver header -/
namespace Hierarchy.DescentOrdinaryDonorHalo.Digit

open DescentHaloWalkRAM DescentHaloDonorChart DescentSharedCableNames
open DescentColonies DescentCableDonorNames DescentSIMDLookup DescentPackedZip DescentHostDirectory
open DescentParallelBase DescentOrdinaryDonorRankDirectory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

private theorem selected_walk {H D : ℕ} (R : Fin H → Fin D → Option (Fin H)) (v u : Fin H)
    (p : Fin (breadth D)) (hit : Gather.select (Gather.reaching R) v p=some u) :
    walk R v (path p) 4=some u :=by
  unfold Gather.select at hit
  split at hit
  · contradiction
  · exact hit

/-- At this receiver the purchased order reserves one radix block per original walk rank. -/
theorem measured_slot {H D k : ℕ} {J V U C : Type} [Fintype U] [DecidableEq J] [DecidableEq V]
    (near : V → Finset V) (name : V↪Fin H) (R : Fin H → Fin D → Option (Fin H))
    (listed : ∀v u,u∈near v → ∃i,R (name v) i=some (name u))
    (pos : U → J×V) (block : U → Block k) (coords : Function.Injective fun u=>(pos u,block u))
    (whereAt : C → Key (J×V)) (c : C) (donor : U)
    (inside : donor∈(DescentHaloCompilation.atSource near name R listed pos block coords whereAt).member c) :
    let index:=Ranks.earlier (Rebase.terminal R) (name (whereAt c).1.2) (name (pos donor).2).val
    let slot:=(DescentHaloCompilation.atSource near name R listed pos block coords whereAt).slot c ⟨donor,inside⟩
    index<breadth D ∧ index*2^k+(block donor).val=slot.val :=by
  intro index slot
  have value : index*2^k+(block donor).val=slot.val :=by
    change _=(finProdFinEquiv (rank R (name (whereAt c).1.2) (name (pos donor).2) _,block donor)).val
    have endpoints : Rebase.terminal R=endpoint R:=rfl
    simp [index,finProdFinEquiv_apply_val,rank,endpoints,Nat.mul_comm,Nat.add_comm]
  refine ⟨?_,value⟩
  by_contra! large
  have lower:=Nat.mul_le_mul_right (2^k) large
  have upper:=slot.isLt
  omega

/-- The local rank is measured at the receiver of the private operand. Its old
block is the donor node's block. This also covers the empty walk to the receiver. -/
theorem from_local_rank {H D k : ℕ} {J V U C : Type} [Fintype U] [DecidableEq J] [DecidableEq V]
    (near : V → Finset V) (name : V↪Fin H) (R : Fin H → Fin D → Option (Fin H))
    (listed : ∀v u,u∈near v → ∃i,R (name v) i=some (name u))
    (pos : U → J×V) (block : U → Block k) (coords : Function.Injective fun u=>(pos u,block u))
    (whereAt : C → Key (J×V)) (c : C) (donor : U)
    (inside : donor∈(DescentHaloCompilation.atSource near name R listed pos block coords whereAt).member c)
    (p : Fin (breadth D)) (hit : Gather.select (Gather.reaching R) (name (whereAt c).1.2) p=some (name (pos donor).2))
    (out : ℕ) (room : breadth D*2^k ≤ 2^out) :
    let receiver:=name (whereAt c).1.2
    let digit:=Packed.token (some (ParentFilter.localRank R receiver p))
    (numeral (breadth D) k out (block donor) digit).val=
      ((DescentHaloCompilation.atSource near name R listed pos block coords whereAt).slot c ⟨donor,inside⟩).val :=by
  dsimp only
  let receiver:=name (whereAt c).1.2
  let old:=name (pos donor).2
  have walk:=selected_walk R receiver old p hit
  have label : Rebase.terminal R receiver p=old.val:=by
    change number (DescentHaloWalkRAM.walk R receiver (path p) 4)=old.val
    simp [walk,number]
  rw [numeral_rank]
  let slot:=(DescentHaloCompilation.atSource near name R listed pos block coords whereAt).slot c ⟨donor,inside⟩
  have same : (ParentFilter.localRank R receiver p).val*2^k+(block donor).val=slot.val :=by
    change Ranks.earlier (Rebase.terminal R) receiver (Rebase.terminal R receiver p)*2^k+(block donor).val=slot.val
    rw [label]
    exact (measured_slot near name R listed pos block coords whereAt c donor inside).2
  rw [Fin.val_cast_of_lt (same.trans_lt (slot.isLt.trans_le room))]
  exact same

/-- A missing or duplicate endpoint has the physical host sentinel. The
separate zero-based rank column can contain zero for a legitimate first rank. -/
def localWord (H P : ℕ) {w : ℕ} (visit entry : Word w) : Cell (Packed.bits P) :=
  if visit.val=H then 0 else ((entry.val+1:ℕ):Cell (Packed.bits P))

variable {H D w : ℕ} (R : Fin H → Fin D → Option (Fin H)) (B : DescentOrdinaryDonorRankDirectory.Banks) (m : Memory w)
    (recorded : DescentOrdinaryDonorRankDirectory.Reads R B m)
local notation "P" => breadth D
include recorded

theorem local_word (v : Fin H) (p : Fin P) (hosts : H < 2^w) (paths : P ≤ 2^w) :
    localWord H P (m (B.endpoints.base+(Ranks.id v p).val)) (m (B.localRank.base+(Ranks.id v p).val))=Packed.token ((Gather.select (Gather.reaching R) v p).map (fun _=>ParentFilter.localRank R v p)) :=by
  rw [recorded.visit v p,recorded.localValue v p]
  have fit : Ranks.earlier (Rebase.terminal R) v (Rebase.terminal R v p)<2^w:=(ParentFilter.localRank R v p).isLt.trans_le paths
  cases seen : Gather.select (Gather.reaching R) v p with
  | none=>
    change (if ((H:Word w).val)=H then _ else _)=0
    simp [Fin.val_cast_of_lt hosts]
  | some u=>
    change (if ((u.val:Word w).val)=H then _ else _)=Packed.token (some (ParentFilter.localRank R v p))
    rw [Fin.val_cast_of_lt (u.isLt.trans hosts),ite_eq_right u.isLt.ne,Fin.val_cast_of_lt fit]
    apply Fin.ext
    exact Fin.val_cast_of_lt (Packed.token (some (ParentFilter.localRank R v p))).isLt

theorem local_padded (v : Fin H) (p : Fin P) (hosts : H < 2^w) (paths : P ≤ 2^w)
    (missing : Gather.select (Gather.reaching R) v p=none) (k out : ℕ) (b : Block k) :
    numeral P k out b (localWord H P (m (B.endpoints.base+(Ranks.id v p).val)) (m (B.localRank.base+(Ranks.id v p).val)))=0 :=by
  rw [local_word R B m recorded v p hosts paths,missing]
  exact numeral_hole P k out b

theorem from_local_word {k : ℕ} {J V U C : Type} [Fintype U] [DecidableEq J] [DecidableEq V]
    (near : V → Finset V) (name : V↪Fin H)
    (listed : ∀v u,u∈near v → ∃i,R (name v) i=some (name u))
    (pos : U → J×V) (block : U → Block k) (coords : Function.Injective fun u=>(pos u,block u))
    (whereAt : C → Key (J×V)) (c : C) (donor : U)
    (inside : donor∈(DescentHaloCompilation.atSource near name R listed pos block coords whereAt).member c)
    (p : Fin P) (hit : Gather.select (Gather.reaching R) (name (whereAt c).1.2) p=some (name (pos donor).2))
    (out : ℕ) (hosts : H < 2^w) (paths : P ≤ 2^w) (room : P*2^k ≤ 2^out) :
    (numeral P k out (block donor) (localWord H P (m (B.endpoints.base+(Ranks.id (name (whereAt c).1.2) p).val)) (m (B.localRank.base+(Ranks.id (name (whereAt c).1.2) p).val)))).val=
      ((DescentHaloCompilation.atSource near name R listed pos block coords whereAt).slot c ⟨donor,inside⟩).val :=by
  rw [local_word R B m recorded _ p hosts paths,hit]
  exact from_local_rank near name R listed pos block coords whereAt c donor inside p hit out room

end
end Hierarchy.DescentOrdinaryDonorHalo.Digit

end OAI
