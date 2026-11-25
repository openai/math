import OAI.Hierarchy.ProtocolRAMCataloguePartition
import OAI.Hierarchy.ProbePrivateSwitch
import OAI.Hierarchy.TaggedWideFreeEdges
import OAI.Hierarchy.TaggedWideHost

namespace OAI
/-! # The fixed private switches of the original native report catalogue -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open ProbeStage ProbeStage.CoreBoard TaggedShorterZero Computability.VPVNP.BurstRAM
open ThreeFlat Routing Diagonal TraceWords
open scoped Classical BigOperators
variable {F : Type*} [Field F] {h W k : ℕ} {S : PurchaseSampler}
    (b : Board) (order : Fin b.coreRows ≃ Edges S h (2^W) k)

def Board.transport (i : Fin b.rows) : Prop :=
  match b.partition order i with | .inl _ => False | .inr _ => True

abbrev Board.Private := {i : Fin b.rows // ¬b.transport order i}

/-- The physical switches are indexed in the native report's permanent
order. Every positive-scale slot, including a vacant acquisition, lies in
the complementary set. -/
def Board.freeOrdinal : Free S h (2^W) k ≃ b.Private order :=
  Equiv.ofBijective (fun f=>⟨b.coreIndex (order.symm (.inl f)),by
    simp [Board.transport,b.private_row order f]⟩) (by
    constructor
    · intro f g eqn
      have same := congrArg (fun z : b.Private order=>b.partition order z.val) eqn
      simpa only [b.private_row,Sum.inl.injEq] using same
    · rintro ⟨i,privateRow⟩
      cases found : b.partition order i with
      | inl f =>
        exact ⟨f,Subtype.ext ((b.partition order).injective ((b.private_row order f).trans found.symm))⟩
      | inr z => exact (privateRow (by simp [Board.transport,found])).elim)

variable {address wordBits width : ℕ} (fits : siteLast h (2^W) k+1≤2^address) (room : width≤2^wordBits)
local notation "names" => fun (f : Free S h (2^W) k) side=>privateNames f fits side 0

/-- The native row prints its smaller global CPU site first. The public
orientation of a private link therefore determines which word feeds each
end of its switch without any selector-dependent data movement. -/
def Board.freeSide (i : b.Private order) (side : Bool) : Bool :=
  let f := (b.freeOrdinal order).symm i
  if (names f false).val≤(names f true).val then side else !side

theorem Board.oriented (i : b.Private order) (ends : Bool→Word address)
    (low : (ends false).val=min (names ((b.freeOrdinal order).symm i) false).val
      (names ((b.freeOrdinal order).symm i) true).val)
    (high : (ends true).val=max (names ((b.freeOrdinal order).symm i) false).val
      (names ((b.freeOrdinal order).symm i) true).val) (side : Bool) :
    ends (b.freeSide order fits i side)=names ((b.freeOrdinal order).symm i) side := by
  by_cases forward : (names ((b.freeOrdinal order).symm i) false).val≤(names ((b.freeOrdinal order).symm i) true).val
  · cases side <;> apply Fin.ext <;> simp [Board.freeSide,forward,low,high]
  · have rev := le_of_not_ge forward
    cases side <;> apply Fin.ext <;> simp [Board.freeSide,forward,low,high,rev]

/-- Both endpoint words, the actual native width, and the two shared
payload apertures are read on the same physical fixed board. -/
def Board.privatePin {V : Type} (ep : Fin b.rows→Bool→Fin address→V)
    (cut : Fin b.rows→Fin wordBits→V) (data : Bool→b.Private order→Fin width→V) :
    (i : b.Private order) → Pin 1 1 wordBits address width → V ⊕ Bool :=
  fun i p=>.inl (p.elim (fun z=>z.2.elim
    (fun y=>ep i.val (b.freeSide order fits i y.1) y.2) (cut i.val))
    (fun z=>data z.1 i z.2.2))

theorem Board.private_values {V : Type} [Fintype V] (ep : Fin b.rows→Bool→Fin address→V)
    (cut : Fin b.rows→Fin wordBits→V) (data : Bool→b.Private order→Fin width→V)
    (x : V→Bool) (ends : Fin b.rows→Bool→Word address) (size : Fin b.rows→Word wordBits)
    (record : ∀ i side j,x (ep i side j)=bits (ends i side) j)
    (widthWord : ∀ i j,x (cut i j)=bits (size i) j)
    (printed : ∀i : b.Private order, 0<(size i.val).val →
      let f := (b.freeOrdinal order).symm i
      (ends i.val false).val=min (names f false).val (names f true).val ∧
      (ends i.val true).val=max (names f false).val (names f true).val) :
    let gates := fun i : b.Private order=>privateSwitch (F:=F) ((b.freeOrdinal order).symm i) fits room
    TypedWiring.value (Tagged.WideHost.localFamily gates (b.privatePin order fits ep cut data)) x =
      ∏ i : b.Private order,
        if ∀j : Fin width,j.val<(size i.val).val → x (data false i j)=x (data true i j) then 1 else 0 := by
  intro gates
  rw [Tagged.WideHost.localFamily_eval]
  apply Finset.prod_congr rfl
  intro i _
  let f := (b.freeOrdinal order).symm i
  let e := fun (_ : Fin 1) (side : Bool)=>ends i.val (b.freeSide order fits i side)
  let u := fun _ : Fin 1=>size i.val
  let a := fun (side : Bool) (_ : Fin 1) (j : Fin width)=>x (data side i j)
  have wires : Sum.elim x id ∘ b.privatePin order fits ep cut data i=pins e u a := by
    funext z
    rcases z with ⟨_,⟨side,j⟩|j⟩|⟨side,_,j⟩
    · exact record ..
    · exact widthWord ..
    · rfl
  rw [wires]
  exact private_read f fits room u e a (fun live side=>b.oriented order fits i _ (printed i live).1 (printed i live).2 side)

/-- The installed cost includes every original private ordinal even when
its width is zero. Its absolute row count bounds the private family. -/
theorem Board.private_cost {V : Type} [Fintype V] (ep : Fin b.rows→Bool→Fin address→V)
    (cut : Fin b.rows→Fin wordBits→V) (data : Bool→b.Private order→Fin width→V) :
    let gates := fun i : b.Private order=>privateSwitch (F:=F) ((b.freeOrdinal order).symm i) fits room
    let net := Tagged.WideHost.localFamily gates (b.privatePin order fits ep cut data)
    net.cells+net.internal≤b.rows*(2+2*(2*(100*address+100)+width*(100*wordBits+100))) := by
  intro gates net
  rw [show net.cells+net.internal=∑i,((gates i).cells+(gates i).internal) from Tagged.WideHost.localFamily_size ..]
  apply (Finset.sum_le_sum (fun i _=>private_price (F:=F) ((b.freeOrdinal order).symm i) fits room)).trans
  simp

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI
