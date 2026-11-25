import OAI.Hierarchy.TaggedWideCalendarPrivate
import OAI.Hierarchy.TaggedWideSwitchTariff

namespace OAI
/-! # Two physically shared data bits at each fixed private ordinal -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open ThreeFlat Routing
open ProbeStage ProbeStage.CoreBoard Tagged WidePadding WideCalendarSites WideStack WideStack.Leaf
open Computability.VPVNP.BurstRAM Diagonal TraceWords
open scoped Classical BigOperators
variable {F V : Type} [Field F] [Fintype V] {S : PurchaseSampler} {h W k width b : ℕ}
    (board : Board) (order : Fin board.coreRows ≃ Edges S h (2^W) k)
    (room : width≤2^b) (cut : Fin board.rows→Fin b→V) (data : Bool→board.Private order→Fin width→V)

local notation "B" => board.Private order × Fin width
local notation "read" => (Fintype.equivFin B).symm

/-- One equality cell on the two physically retained private copies. Above the
reported width the two independent padding masks force both copies to zero. -/
def Board.equalCopies : BitNetwork F (Fintype.card V) where
  internal := 0
  cells := Fintype.card B
  source i a := .pin (Fintype.equivFin V (data (decide (a.val=1)) (read i).1 (read i).2))
  table _ x := if x 0=x 1 then 1 else 0

theorem Board.equalCopies_value (v : V→Bool) :
    TypedWiring.value (board.equalCopies (F:=F) order data) v =
      if ∀r j,v (data false r j)=v (data true r j) then 1 else 0 := by
  unfold TypedWiring.value BitNetwork.eval BitNetwork.weight BitNetwork.factor
  simp only [Board.equalCopies,BitSource.read,Equiv.symm_apply_apply]
  change (∑ _ : Fin 0 → Bool, ∏i : Fin (Fintype.card B),if v (data false (read i).1 (read i).2)=
    v (data true (read i).1 (read i).2) then (1:F) else 0)=_
  have empty (a : F) : (∑ _ : Fin 0 → Bool, a) = a := by
    simp [Finset.sum_const]
  rw [empty]
  by_cases ok : ∀r j,v (data false r j)=v (data true r j)
  · simp [ok]
  · rw [ite_eq_right ok]
    push Not at ok
    obtain ⟨r,j,bad⟩:=ok
    apply Finset.prod_eq_zero (Finset.mem_univ (Fintype.equivFin B (r,j)))
    simpa only [Equiv.symm_apply_apply] using (ite_eq_right bad :
      (if v (data false r j)=v (data true r j) then (1:F) else 0)=0)

def Board.privateBits : Net F V :=
  attach (board.privatePadding (F:=F) order room cut data) (board.equalCopies (F:=F) order data)

theorem Board.privateBits_value (v : V→Bool) (size : Fin board.rows→Word b)
    (reads : ∀i j,v (cut i j)=bits (size i) j) :
    TypedWiring.value (board.privateBits (F:=F) order room cut data) v =
    if EndsPadded (fun r=>(size r.val).val) (fun _ : board.Private order=>width) (fun side r j=>v (data side r j))
    then ∏i : board.Private order,if ∀j : Fin width,j.val<(size i.val).val →
      v (data false i j)=v (data true i j) then 1 else 0 else 0 := by
  rw [Board.privateBits,attach_value,board.privatePadding_value order room cut data v size reads,
    board.equalCopies_value order data v]
  by_cases padded : EndsPadded (fun r=>(size r.val).val) (fun _ : board.Private order=>width)
      (fun side r j=>v (data side r j))
  · simp only [ite_eq_left padded,one_mul]
    by_cases eq : ∀r j,v (data false r j)=v (data true r j)
    · simp [eq]
    · rw [ite_eq_right eq]
      push Not at eq
      obtain ⟨i,j,bad⟩:=eq
      have active : j.val<(size i.val).val:=by
        by_contra! high
        exact bad ((padded false i j high).trans (padded true i j high).symm)
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact ite_eq_right (fun yes=>bad (yes j active))
  · simp only [ite_eq_right padded,zero_mul]

theorem Board.privateBits_cost :
    let net:=board.privateBits (F:=F) order room cut data
    net.cells+net.internal≤2*Fintype.card (board.Private order)*width*(200*b+65)+
        Fintype.card (board.Private order)*width := by
  intro net
  rw [show net.cells+net.internal=_ from attach_cost ..]
  unfold Board.privatePadding
  rw [WideHost.localFamily_size]
  have hp:=(board.privatePaddingPorts order room cut data).cost (F:=F)
  simpa only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,Finset.univ_unique,
    Finset.sum_singleton,Board.equalCopies,Nat.add_zero,Nat.mul_assoc] using
    Nat.add_le_add_right hp (Fintype.card (board.Private order)*width)

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI
