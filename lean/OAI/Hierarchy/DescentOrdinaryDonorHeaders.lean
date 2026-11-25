import OAI.Hierarchy.DescentDonorRankHeaders
import OAI.Hierarchy.DescentDonorChartTables

namespace OAI
/-! # Simultaneously issued rank and hub headers at the chosen ordinary date -/
namespace Hierarchy.DescentRawCablePanel.DonorHeaders
open DescentHaloWalkRAM DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D H G M w : ℕ} (R : Fin H→Fin D→Option (Fin H)) (flag : Fin H→Bool)
local notation "P" => breadth D

def ordValue (u : Fin H) (p : Fin P) : Fin (P+1) :=
  ⟨observedRank R u p,Nat.lt_succ_of_lt (Ranks.bound (DescentHaloCompilation.reached R) u p)⟩
def tagValue (u : Fin H) (p : Fin P) : Fin (P+1) :=
  ⟨(observedHub R u flag p).toNat, by
    cases observedHub R u flag p with
    | false => exact Nat.succ_pos P
    | true => exact Nat.succ_lt_succ (Nat.zero_lt_of_lt p.isLt)⟩

def shelf (H G M D base addr : ℕ) :=
  DonorChartBook.tables H G M (breadth D) base ⟨addr,Nat.clog 2 (H*breadth D)⟩

theorem native_headers (W : DescentHaloWalkRAM.Banks) (T : Ranks.Columns) (hub : Bank) (ord tags base : ℕ) (m : Memory w)
    (first : DescentHaloWalkRAM.Fits W T.endpoints.base H D w) (second : Ranks.Fits T ord H P w)
    (next : ord+H*P≤tags) (low : tags+H*P≤base) (limit : base+DonorChartBook.words H G M P<2^w)
    (roster : DescentHaloWalkRAM.Reads W R m)
    (heads : ∀(v:Fin H)(p:Fin P),m (T.start.base+(Ranks.id v p).val)=((v.val*P:ℕ):Word w))
    (prior : T.start.base+T.start.size≤T.endpoints.base) (range : H<2^w)
    (hubs : hub.Fits w T.endpoints.base) (amount : H≤hub.size)
    (source : ∀v : Fin H,m (hub.base+v.val)=((flag v).toNat:Word w)) :
    let firstPass:=schedule W T hub ord tags H D w
    let mid:=after W T hub ord tags H D m
    let dest:=DonorChartBook.image H G M P base mid
    (firstPass.seq (DonorChartBook.install H G M P base w)).Exec m dest
      (clocks W T hub H D+(4+10*DonorChartBook.words H G M P)) ∧
      DescentHaloPackedRebase.Reads (shelf H G M D base ord) (ordValue R) M G dest ∧
      DescentHaloPackedRebase.Reads (shelf H G M D base tags) (tagValue R flag) M G dest ∧
      ∀a,a<T.endpoints.base→dest a=m a := by
  intro firstPass mid dest
  obtain ⟨ran,a,b,frame,cheap⟩:=run R flag W T hub ord tags m first second next (low.trans_lt ((Nat.le_add_right ..).trans_lt limit))
    roster heads prior range hubs amount source
  obtain ⟨finish,table,preserve⟩:=DonorChartBook.mount H G M P base mid limit
  have beg : T.endpoints.base≤ord:=(Nat.le_add_right ..).trans second.endpoints.2.2
  refine ⟨ran.then finish,?_,?_,?_⟩
  · apply DonorChartBook.ready H G M P base _ _ dest table
    intro v j
    exact (preserve _ (.inl ((Nat.add_lt_add_left (DescentHaloWalkRAM.row v j).isLt _).trans_le (next.trans ((Nat.le_add_right ..).trans low))))).trans (a v j)
  · apply DonorChartBook.ready H G M P base _ _ dest table
    intro v j
    exact (preserve _ (.inl ((Nat.add_lt_add_left (DescentHaloWalkRAM.row v j).isLt _).trans_le low))).trans (b v j)
  · intro h old
    exact (preserve _ (.inl (by omega))).trans (frame h old)


end
end Hierarchy.DescentRawCablePanel.DonorHeaders

end OAI
