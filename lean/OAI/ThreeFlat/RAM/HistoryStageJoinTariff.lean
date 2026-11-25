import OAI.ThreeFlat.RAM.HistoryStageBoundedResources

namespace OAI
/-! # Instruction cost of the ordered bounded join -/

namespace ThreeFlat.RAM.HistoryBoundedBody.Build

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr HistoryStageBody.Physical

private theorem join_arith (K argc n words : ℕ) (pos : 0<K) :
    (4+9*K)+(13+14*argc*K)+(13+7*argc*K)+(6+38*n+words*K+13+4*K) ≤
      100*K*(1+argc+n+words) := by
  have hn:=Nat.le_mul_of_pos_right n pos
  have p : 1≤K := pos
  ring_nf at hn ⊢
  omega

private theorem join_rates (K argc n words boot cmd arg tape save : ℕ) (pos : 0<K)
    (hb : boot≤K) (hc : cmd≤K) (ha : arg≤K) (ht : tape≤K) (hs : save≤K) :
    (4+9*boot)+(13+14*argc*cmd)+(13+7*argc*arg)+(6+38*n+words*tape+13+4*save) ≤
      100*K*(1+argc+n+words) := by
  apply le_trans _ (join_arith K argc n words pos)
  gcongr

open private HistoryStageBody.Physical.joinPrice HistoryStageBody.Physical.bounded_boot_cost
  HistoryStageBody.Physical.bounded_generator_cost from
  OAI.ThreeFlat.RAM.HistoryStageBoundedResources
open private HistoryStageBody.Physical.readyResources_eq HistoryStageBody.Physical.ready_empty_rows from
  OAI.ThreeFlat.RAM.HistoryStageGenericLeafResources

private theorem join_rate_bounds (ready tape seed save cmd arg : ℕ) (readyCost : 30+4*tape=ready) :
    let rate := 1+HistoryStageBody.Physical.joinPrice ready seed save cmd arg
    2*seed+4≤rate ∧ 2*(cmd+250)+4≤rate ∧ 2*(arg+250)+4≤rate ∧
      2*tape+4≤rate ∧ 2*save+4≤rate := by
  dsimp only [HistoryStageBody.Physical.joinPrice]
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

private theorem join_rate_mono {work allowance rate : ℕ}
    (fit : work≤allowance) (bound : 2*allowance+4≤rate) : 2*work+4≤rate :=
  (Nat.add_le_add_right (Nat.mul_le_mul_left 2 fit) 4).trans bound

/-- The static rate is independent of the address layout and word width.
The charged data are precisely the installed child headers and ordered tape. -/
theorem typed_ticks_le {W n p h : ℕ} {F : Type*} {arity : Fin n→ℕ} (B : Build W)
    (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ) (head : Fin n→HistoryJoinScan.Header ℕ) :
    B.ticks (Tape.tape N wire id head) ≤ 100*(1+joinResources B.cap)*
      (1+B.hub.argc+n+((List.finRange n).map (fun i=>arity i+4*(N i).cells)).sum) := by
  let K:=1+joinResources B.cap
  let zero : Layout:=⟨0,0,0⟩
  obtain ⟨seed,cmd,arg,tape,save⟩ := join_rate_bounds readyResources (HistorySelectedOps.tariff [])
    (boot zero).work (result zero B.cap).work (HistoryBoundedJoin.formula B.cap true).work
    (HistoryBoundedJoin.formula B.cap false).work HistoryStageBody.Physical.readyResources_eq
  have bootRate : 2*(HeaderScan.closed (w:=W) (boot B.layout)).binds+4≤K :=
    join_rate_mono ((HeaderScan.binds_closed (w:=W) (boot B.layout)).trans
      (HistoryStageBody.Physical.bounded_boot_cost B.layout zero)).le seed
  have scanRate (flag : Bool) : 2*(generator W B.layout B.cap flag).binds+4≤K := by
    apply join_rate_mono (HistoryStageBody.Physical.bounded_generator_cost W B.layout B.cap flag)
    cases flag
    · exact arg
    · exact cmd
  have tapeRate : 2*(Tape.expr W).binds+4≤K :=
    join_rate_mono (HistoryStageBody.Physical.ready_empty_rows W) tape
  have endRate : 2*(HeaderScan.closed (w:=W) (result B.layout B.cap)).binds+4≤K :=
    join_rate_mono ((HeaderScan.binds_closed (w:=W) (result B.layout B.cap)).trans
      (result_work B.layout zero B.cap)).le save
  rw [ticks,Tape.tape_cost]
  exact join_rates K B.hub.argc n _ _ _ _ _ _
    (Nat.zero_lt_one.trans_le (Nat.le_add_right 1 (joinResources B.cap)))
    bootRate (scanRate true) (scanRate false) tapeRate endRate


end ThreeFlat.RAM.HistoryBoundedBody.Build

end OAI
