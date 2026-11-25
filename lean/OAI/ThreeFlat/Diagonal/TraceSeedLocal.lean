import OAI.ThreeFlat.Diagonal.TraceSeedWordForm

namespace OAI
/-! # Exact paired endpoint support of an assembled terminal tensor -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM PrivateRAM LaneCursor TraceSuffix HistoryContraction
open scoped BigOperators Classical

private theorem pair_lane {T low lane j : ℕ} (live : j<retained T low lane) :
    ((laneStart low lane+j)/2)/2^low=lane := by
  have short : j<2*(2^low) := lt_of_lt_of_le live
    (Nat.mul_le_mul_left 2 (Nat.min_le_left (2^low) (T-lane*2^low)))
  have base : laneStart low lane=2*(lane*2^low) := by unfold laneStart; ring
  have split : (laneStart low lane+j)/2=lane*2^low+j/2 := by rw [base]; omega
  rw [split,Nat.mul_comm lane (2^low),Nat.mul_add_div (Nat.two_pow_pos low),
    Nat.div_eq_of_lt (show j/2<2^low by omega),Nat.add_zero]

theorem seedEndpoint_lane {q T low : ℕ} (u : Fin (q+1)×Lane (q+1)) (j : Fin (seedExt T low u)) :
    u.1=0 ∧ (seedEndpoint T low u j).val/2/2^low=(finFunctionFinEquiv u.2).val := by
  by_cases zero : u.1=0
  · exact ⟨zero,pair_lane (by simpa only [seedExt,zero,ite_true] using j.isLt)⟩
  · have empty:=j.isLt
    simp [seedExt,zero] at empty

variable {F : Type} [Field F] [Fintype F] {w p r k S base f q low T : ℕ}
variable (M : Machine w p r k) (t : NativeTrace.Fits M S base ((q+1)+low) f)
  (hF : Fintype.card F≤2^w) (st : Word w) (B : PhysicalStage.Block F) (hk : 2≤q+1)
variable (span : 2*T≤S)

/-- For the true paired input, only zero-cursor ancestors read endpoints.
The arithmetic equality gives their exact physical pair ordinals even in a
partially occupied final lane. This applies to every boundary at the terminal site. -/
theorem seedForest_local (P : Plan F (B.cursorState hk low (1+(((q+1)+low)+((q+1)+low)))
    (TraceStaticRow.gateTable hF t.width t.labels base f st r k ((q+1)+low)).cells).shape) (h : P.History) (v : (P.finish h).Site)
    (assembly : P.Assembly (seedWordLayout M t hF st B hk span).ports.form) (N : Forest F (seedWordLayout M t hF st B hk span).ports.form) (x y x' y' : Fin T→Bool)
    (same : ∀ lane : Lane (q+1), P.destination h (0,lane)=v → ∀ j : Fin T,
      j.val/2^low=(finFunctionFinEquiv lane).val → x j=x' j ∧ y j=y' j) :
    (P.assemble h assembly N).1.values (P.assemble h assembly N).2 (endpointPin x y) v =
      (P.assemble h assembly N).1.values (P.assemble h assembly N).2 (endpointPin x' y') v := by
  let ports := (seedWordLayout M t hF st B hk span).ports
  have left := congrFun (P.assemble_values h ports.form assembly N (endpointPin x y)) v
  have right := congrFun (P.assemble_values h ports.form assembly N (endpointPin x' y')) v
  refine left.trans (Eq.trans ?_ right.symm)
  apply P.cells_local h v
  rintro ⟨cursor,lane⟩ dest
  have ext : ports.pin (cursor,lane) (endpointPin x y)=ports.pin (cursor,lane) (endpointPin x' y') := by
    funext j
    change Fin (seedExt T low (cursor,lane)) at j
    by_cases first : cursor=0
    · subst cursor
      have live : j.val<retained T low (finFunctionFinEquiv lane).val := by
        simpa only [seedExt,ite_true,eq_self] using j.isLt
      let i := laneStart low (finFunctionFinEquiv lane).val+j.val
      have bound : i<2*T := at_true live
      let z : Fin T := ⟨i/2,by omega⟩
      have owned : z.val/2^low=(finFunctionFinEquiv lane).val := pair_lane live
      obtain ⟨old,fresh⟩ := same lane dest z owned
      change (if i%2=0 then x z else y z)=(if i%2=0 then x' z else y' z)
      split <;> assumption
    · have impossible := j.isLt
      simp [seedExt,first] at impossible
  funext boundary
  change (N (cursor,lane)).compile.eval (Fin.append (ports.pin (cursor,lane) (endpointPin x y)) (ports.encode (cursor,lane) boundary)) =
    (N (cursor,lane)).compile.eval (Fin.append (ports.pin (cursor,lane) (endpointPin x' y')) (ports.encode (cursor,lane) boundary))
  exact congrArg (fun pins => (N (cursor,lane)).compile.eval
    (Fin.append pins (ports.encode (cursor,lane) boundary))) ext


end ThreeFlat.Diagonal.TraceBitHeader

end OAI
