import OAI.Hierarchy.DescentDatedLocalDonorDigit
import OAI.Hierarchy.DescentDatedPriorHeaderReceipt

namespace OAI
/-! # The local private key read from the actual original four-walk header -/
namespace Hierarchy.DescentDatedAddressBook.PriorHeader
open DescentHaloWalkRAM DescentOrdinaryDonorHalo DescentParallelBase DescentSharedCableNames DescentHostDirectory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentSIMDLookup DescentColonies DescentCableDonorNames
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M D w : ℕ} (base : ℕ) (adj : Bank) (ok : Room adj H G M D base w)
  (m : Memory w) (R : Fin H → Fin D → Option (Fin H))
  (old : ∀(v : Fin H) (j : Fin D),m (adj.base+v.val*D+j.val)=(number (R v j):Word w))
local notation "P" => breadth D
local notation "b" => rankBanks H G M D base
local notation "mem" => image H G M D base adj m

def donorWord (v : Fin H) (p : Fin P) :=Digit.localWord H P
  (mem ((b).endpoints.base+(Ranks.id v p).val)) (mem ((b).localRank.base+(Ranks.id v p).val))

include ok old
theorem donor_word (v : Fin H) (p : Fin P) : donorWord (G:=G) (M:=M) (D:=D) base adj m v p=
    Packed.token ((Gather.select (Gather.reaching R) v p).map (fun _=>ParentFilter.localRank R v p)) :=
  Digit.local_word R b mem (directory base adj ok m R old) v p ok.hosts ok.paths.le

theorem donor_slot {k : ℕ} {J V U C : Type} [Fintype U] [DecidableEq J] [DecidableEq V]
    (near : V → Finset V) (name : V↪Fin H)
    (listed : ∀v u,u∈near v → ∃i,R (name v) i=some (name u))
    (pos : U → J×V) (block : U → Block k) (coords : Function.Injective fun u=>(pos u,block u))
    (whereAt : C → Key (J×V)) (c : C) (donor : U)
    (inside : donor∈(DescentHaloCompilation.atSource near name R listed pos block coords whereAt).member c)
    (p : Fin P) (hit : Gather.select (Gather.reaching R) (name (whereAt c).1.2) p=some (name (pos donor).2))
    (out : ℕ) (room : P*2^k ≤ 2^out) :
    (Digit.numeral P k out (block donor) (donorWord (G:=G) (M:=M) (D:=D) base adj m (name (whereAt c).1.2) p)).val=
      ((DescentHaloCompilation.atSource near name R listed pos block coords whereAt).slot c ⟨donor,inside⟩).val :=
  Digit.from_local_word R b mem (directory base adj ok m R old) near name listed pos block coords whereAt
    c donor inside p hit out ok.hosts ok.paths.le room

theorem donor_absent (v : Fin H) (p : Fin P) (missing : Gather.select (Gather.reaching R) v p=none)
    (k out : ℕ) (block : Block k) :
    Digit.numeral P k out block (donorWord (G:=G) (M:=M) (D:=D) base adj m v p)=0 :=
  Digit.local_padded R b mem (directory base adj ok m R old) v p ok.hosts ok.paths.le missing k out block

/-- At a captured occurrence the forward path indexes the reverse-rank word
at the old donor's host. Its original block identifies the donor at the receiver. -/
theorem captured_slot {k : ℕ} {J V U C : Type} [Fintype U] [DecidableEq J] [DecidableEq V]
    (near : V → Finset V) (name : V ↪ Fin H)
    (listed : ∀v u,u∈near v → ∃i,R (name v) i=some (name u))
    (reciprocal : ∀v u i,R v i=some u → ∃j,R u j=some v)
    (pos : U → J×V) (block : U → Block k) (coords : Function.Injective fun u=>(pos u,block u))
    (whereAt : C → Key (J×V)) (c : C) (donor : U)
    (inside : donor∈(DescentHaloCompilation.atSource near name R listed pos block coords whereAt).member c)
    (p : Fin P) (hit : walk R (name (pos donor).2) (path p) 4=some (name (whereAt c).1.2)) :
    (mem ((b).reverseRank.base+(Ranks.id (name (pos donor).2) p).val)).val*2^k+(block donor).val=
      ((DescentHaloCompilation.atSource near name R listed pos block coords whereAt).slot c ⟨donor,inside⟩).val :=by
  obtain ⟨_,_,_,rank⟩:=Rebase.actual R reciprocal _ _ p hit
  rw [(directory base adj ok m R old).reverse,Fin.val_cast_of_lt ((Rebase.value_le R .rank _ p).trans_lt ok.paths),rank]
  exact (Digit.measured_slot near name R listed pos block coords whereAt c donor inside).2

end
end Hierarchy.DescentDatedAddressBook.PriorHeader

end OAI
