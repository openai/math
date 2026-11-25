import OAI.Optimization.LinearProgramming.Recovery.PairBuilderPublish

/-! A genuine three-call packed-basis ROM for an arbitrary row-constraint table.
The same routine serves the initial LP and every support-deletion test. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder
open RAM RAM.Block RAM.Call RAM.Callable RAM.Tape Matrix
open _root_.OAI.Optimization.LinearProgramming.Geometry

attribute [local irreducible] RAM.addressBudget RowPack.program ResidualROM.block

private theorem reserve_bounds (row residual : ℕ) :
    row ≤ row + residual ∧ residual ≤ row + residual :=
  ⟨Nat.le_add_right row residual, Nat.le_add_left residual row⟩

/-- From the actual caller input, physically pack independent spanning rows, construct
the kernel projector, pack its rows and publish both bases to the normal subspace ABI. -/
theorem program_run {h n : ℕ} (rev : Bool) (l : Layout h n) (C : Matrix (Fin h) (Fin n) ℚ)
    (native caller : Memory ℚ) (H e : ℕ) (roots : InputRegs l caller)
    (table : uniformRect h n l.src caller=C) (data : ∀i j,ratBits (C i j) ≤ e)
    (hn : Within H native) (hc : Within H caller) (foot : Footprint l.previous (native.atPC 0)) :
    let W := max H (pairWidth h n e)
    ∃ (front back : Memory ℚ) (k s : ℕ) (F : Matrix (Fin k) (Fin n) ℚ) (R : Matrix (Fin s) (Fin n) ℚ),
      (program rev).Run (fun x=>ratBits x ≤ W) (Odd.memory native caller) (time l) (Odd.memory front back) ∧
      Within W front ∧ Within W back ∧ Footprint (capacity h n l.previous-1) (front.atPC 0) ∧ SourceFrame l caller back ∧
      Prepared rev l C F R back ∧ k ≤ h ∧ (∀i j,ratBits (F i j) ≤ rowWidth h n e) ∧
      ∀i j,ratBits (R i j) ≤ rowWidth n n (residualWidth n n (rowWidth h n e)) := by
  let e₁:=rowWidth h n e
  let e₂:=residualWidth n n e₁
  let e₃:=rowWidth n n e₂
  let W:=max H (pairWidth h n e)
  let P:=fun x : ℚ=>ratBits x ≤ W
  have hH : H ≤ W := le_max_left ..
  have highs : max (max 3 e₁) (max e₂ e₃) ≤ W := le_max_right ..
  have h3 : 3 ≤ W := ((le_max_left ..).trans (le_max_left ..)).trans highs
  have h₁ : e₁ ≤ W := ((le_max_right ..).trans (le_max_left ..)).trans highs
  have h₂ : e₂ ≤ W := ((le_max_left ..).trans (le_max_right ..)).trans highs
  have h₃ : e₃ ≤ W := ((le_max_right ..).trans (le_max_right ..)).trans highs
  have safeN : native.AllData P := fun j=>(hn j).trans hH
  have safeC : caller.AllData P := fun j=>(hc j).trans hH
  have zero : P 0 := h3
  have addressBounds : addressBudget rowROM ≤ codeReserve ∧ addressBudget ResidualROM.program ≤ codeReserve := by
    unfold codeReserve
    with_reducible exact reserve_bounds (addressBudget rowROM) (addressBudget ResidualROM.program)
  have clear : capacity h n l.previous-1<capacity h n l.previous := by have hp:=pair_fits h n l.previous; omega
  obtain ⟨m₀,r₀,s₀,q₀,v₀⟩:=init_run l native caller roots P safeN safeC
  obtain ⟨u₁,c₁,k,t₁,w₁,rank₁,kh,kn,packs₁⟩:=row_run C e data
  let F:=uniformRect k n (u₁.index 57) u₁
  have pF : PacksRows C F := packs₁
  have bF (i : Fin k) (j : Fin n) : ratBits (F i j) ≤ e₁ := w₁.safe_end _
  obtain ⟨m₁,r₁,s₁,f₁,v₁,a₁,n₁⟩:=loaded_call .first RowPack.program native m₀ u₁ P (fun x=>ratBits x ≤ e₁) v₀ C
    ((matrix_frame q₀.data).trans table) l.previous foot (old_fits ..) safeN s₀ zero (fun _ h=>h.trans h₁)
    addressBounds.1 (t₁.trans (row_time_bound (by omega))) w₁
  obtain ⟨m₂,r₂,s₂,v₂,matF,saveF⟩:=first_export rev u₁ m₁ P v₁ f₁ s₁ k rank₁ kn
  let lower:=firstDst rev l.out n k
  let upper:=secondDst rev l.out n k
  have rowloc : uniformRect k n lower m₂=F := matF
  have firstRoom := first_range rev l k kn
  have workRoom := l.outputRoom
  have srcRoom := l.sourceRoom
  have baseRoom := l.minimum
  have lo : 5 ≤ lower := by dsimp [lower]; omega
  have hi : 5 ≤ upper := by cases rev <;> simp [upper,secondDst] <;> omega
  obtain ⟨u₂,c₂,t₂,w₂,at₂⟩:=residual_run F e₁ bF pF.independent
  have bound₂ := residualWidth_mono (n:=n) (e:=e₁) kn
  obtain ⟨m₃,r₃,s₃,f₃,v₃,a₃,n₃⟩:=loaded_call .residual ResidualROM.block u₁ m₂ u₂ P (fun x=>ratBits x ≤ residualWidth k n e₁)
    v₂ F rowloc _ n₁ clear f₁ s₂ zero (fun _ hb=>(hb.trans bound₂).trans h₂) addressBounds.2
    (t₂.trans (residual_time_bound (by omega))) w₂
  obtain ⟨m₄,r₄,s₄,v₄,matK,saveK⟩:=simple_export .residual u₂ m₃ P v₃ f₃ s₃ (by change 5 ≤ l.scratch; omega)
  have kerloc : uniformRect n n l.scratch m₄=kernelRows F := matK.trans at₂
  have bits₂ (i j : Fin n) : ratBits (kernelRows F i j) ≤ e₂ := by rw [←at₂]; exact (w₂.safe_end _).trans bound₂
  obtain ⟨u₃,c₃,s,t₃,w₃,rank₃,sn,_,packs₃⟩:=row_run (kernelRows F) e₂ bits₂
  let R:=uniformRect s n (u₃.index 57) u₃
  have pR : PacksRows (kernelRows F) R := packs₃
  have bR (i : Fin s) (j : Fin n) : ratBits (R i j) ≤ e₃ := w₃.safe_end _
  have dim := (kernelPair_spec C F R pF pR).2.2.2.1
  obtain ⟨m₅,r₅,s₅,f₅,v₅,a₅,n₅⟩:=loaded_call .last RowPack.program u₂ m₄ u₃ P (fun x=>ratBits x ≤ e₃) v₄ (kernelRows F)
    kerloc _ n₃ clear f₃ s₄ zero (fun _ hb=>hb.trans h₃) addressBounds.1 (t₃.trans (row_time_bound (by omega))) w₃
  obtain ⟨m₆,r₆,s₆,v₆,matR,saveR⟩:=last_export u₃ m₅ P v₅ f₅ s₅ s rank₃ sn hi
  have persist₃ : uniformRect k n lower m₃=F := (matrix_frame a₃.data).trans rowloc
  have persist₄ : uniformRect k n lower m₄=F := (saveK.table lo (Or.inl (firstRoom.2.trans workRoom))).trans persist₃
  have persist₅ : uniformRect k n lower m₅=F := (matrix_frame a₅.data).trans persist₄
  have persist₆ : uniformRect k n lower m₆=F := (saveR.table lo (first_second_disjoint rev dim)).trans persist₅
  obtain ⟨z,done,sz,ending,raw⟩:=finish rev u₃ m₆ P v₆ f₅ s₆ F R persist₆ matR dim
  have secondRoom:=second_range rev l k s dim
  have framed : SourceFrame l caller z := q₀.passive.source.trans (a₁.source.trans ((saveF.output firstRoom.1 firstRoom.2).trans
    (a₃.source.trans (saveK.workspace.trans (a₅.source.trans ((saveR.output secondRoom.1 secondRoom.2).trans ending.source))))))
  refine ⟨u₃,z,k,s,F,R,(r₀.seq (r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (r₆.seq done))))))).mono ?_,f₅,sz,n₅,framed,
    ⟨dim,pF,pR,(matrix_frame ending.data).trans persist₆,(matrix_frame ending.data).trans matR,raw⟩,kh,bF,bR⟩
  unfold time callCost exportCost
  simp only [Nat.mul_assoc]; omega
end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI
