import OAI.Hierarchy.DescentHaloRankRAM

namespace OAI
/-! # Native row ranks from the physically printed four-hop endpoints -/
namespace Hierarchy.DescentHaloCompilation
open DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H D w : ℕ} (R : Fin H→Fin D→Option (Fin H))

def reached (v : Fin H) (p : Fin (breadth D)) := number (walk R v (path p) 4)

private def rankResult (P Q : Procedure w) (m result : Memory w) (t u : ℕ) (rankData : Prop) : Prop :=
  (P.seq Q).Exec m result (t+u) ∧ rankData ∧ CheapCode (P.seq Q)

private theorem join_rank_scans {P Q : Procedure w} {m mid result : Memory w} {t u : ℕ}
    {walkData rankData : Prop} (first : P.Exec m mid t ∧ walkData ∧ CheapCode P)
    (second : walkData → Q.Exec mid result u ∧ rankData ∧ CheapCode Q) :
    rankResult P Q m result t u rankData := by
  obtain ⟨walkExec,rows,walkCheap⟩:=first
  obtain ⟨rankExec,ranked,rankCheap⟩:=second rows
  exact ⟨@Procedure.Exec.then w P Q m mid result t u (@walkExec) (@rankExec),ranked,
    @ProtocolRAM.cheap_seq w P Q (@walkCheap) (@rankCheap)⟩

private theorem input_after_walk (T : Ranks.Columns) (m mid : Memory w)
    (rows : ∀ (v : Fin H) (p : Fin (breadth D)),mid (T.endpoints.base+(row v p).val)=(reached R v p : Word w))
    (frame : ∀ a, a<T.endpoints.base → mid a=m a)
    (header : ∀ (v : Fin H) (p : Fin (breadth D)),m (T.start.base+(Ranks.id v p).val)=((v.val*breadth D:ℕ):Word w))
    (before : T.start.base+T.start.size≤T.endpoints.base) (room : H*breadth D≤T.start.size)
    (word : H<2^w) : Ranks.Reads T (reached R) mid := by
  refine ⟨?_,?_,?_⟩
  · intro v p
    have address : (row v p).val=v.val*breadth D+p.val := by
      simp only [row,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
    rw [←address]
    exact rows v p
  · intro v p
    have ix:=(Ranks.id v p).isLt
    exact (frame _ (by omega)).trans (header v p)
  · intro v p
    unfold reached number
    cases h : walk R v (path p) 4 with
    | none => exact word
    | some e => exact e.isLt.trans word

set_option maxHeartbeats 1200000 in
theorem rank_rows (W : DescentHaloWalkRAM.Banks) (T : Ranks.Columns) (out : ℕ)
    (first : Fits W T.endpoints.base H D w) (second : Ranks.Fits T out H (breadth D) w)
    (m : Memory w) (input : Reads W R m)
    (header : ∀(v:Fin H)(p:Fin (breadth D)),m (T.start.base+(Ranks.id v p).val)=((v.val*breadth D:ℕ):Word w))
    (before : T.start.base+T.start.size≤T.endpoints.base) :
    let n:=H*breadth D
    let f:=body W H D 4
    let g:=Ranks.body T (breadth D)
    let mid:=image T.endpoints.base n f m
    let result:=image out n g mid
    rankResult (scan w T.endpoints.base n f) (scan w out n g) m result
      (4+n*(2*f.work+4)) (4+n*(2*g.work+4))
      (∀(v:Fin H)(p:Fin (breadth D)),result (out+(row v p).val)=(Ranks.earlier (reached R) v (reached R v p):Word w)) :=by
  intro n f g mid result
  refine @join_rank_scans w (scan w T.endpoints.base n f) (scan w out n g) m mid result
    (4+n*(2*f.work+4)) (4+n*(2*g.work+4))
    (∀ (v : Fin H) (p : Fin (breadth D)),mid (T.endpoints.base+(row v p).val)=(reached R v p:Word w))
    (∀ (v : Fin H) (p : Fin (breadth D)),result (out+(row v p).val)=(Ranks.earlier (reached R) v (reached R v p):Word w))
    (DescentHaloWalkRAM.run W T.endpoints.base first R m input) ?_
  intro rows
  have load := input_after_walk R T m mid rows
    (fun a ha=>ProtocolRAMGeneratedWrite.frame_image T.endpoints.base n f m a (.inl ha))
    header before second.sizeStart first.sentinel
  exact Ranks.run T out second (reached R) mid load


end
end Hierarchy.DescentHaloCompilation

end OAI
