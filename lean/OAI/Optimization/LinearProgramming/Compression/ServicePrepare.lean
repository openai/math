import OAI.Optimization.LinearProgramming.Compression.ServicePrepareProgram
import OAI.Optimization.LinearProgramming.Compression.ServiceBudget
import OAI.Optimization.LinearProgramming.Compression.ServicePosition
import OAI.Optimization.LinearProgramming.Compression.ServiceInspected
import OAI.Optimization.LinearProgramming.Compression.ServiceMagnitudeView

/-! Assemble the ordinary table representation into an isolated, finite, canonical
numerical solver input while preserving the stored matrices, old generators and incoming
candidate in the odd physical scalar cells. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServicePrepare

open RAM GeneratorTable ServiceBudget

private def controls : List ℕ := [1,5,7,14,17,18,19,20,21,22]
private theorem control_frames {i : ℕ} (h : i∈controls) :
    i ≠ 27 ∧ i∉[24,26,28,30,32,34] ∧ i∉[8,9,10,11,12,24,25] := by
  simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
  omega

structure Ready {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (J : Finset (NonzeroPairMinor D E)) (u : NonzeroPairMinor D E) (cap : ℕ) (src t : Memory ℚ) : Prop where
  evenScalar : ∀ i, 2*i ≤ cap → t.data (2*i)=(List.ofFn (matrixMinorCache D E J u))[i]?.getD 0
  evenAddress : ∀ i, 2*i ≤ cap → t.index (2*i)=2*([n,J.card,(matrixMinorPosition J u).isSome.toNat,
    rank u J.sort] : List ℕ)[i]?.getD 0
  oddBound : ∀ i, 2*i+1 ≤ cap → t.index (2*i+1) ≤ ServiceFill.oddAddressBudget (live n J.card) n
  oddScalar : ∀ i, 1 ≤ i → i < live n J.card → i ≠ 5 → i ≠ 6 → t.data (2*i+1)=src.data i
  length : t.index 1=live n J.card
  position : t.index 3=rank u J.sort
  table : ServiceClean.TableWords (tableBase n) (stride n) (slotBase n J.card) (slotBase n (J.card+1)) t

theorem run {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (time : Polynomial ℕ) (rom H : ℕ) (J : Finset (NonzeroPairMinor D E)) (u : NonzeroPairMinor D E)
    (s : Memory ℚ) (ins : Inspected D E J u H s) (words : MagnitudeTape D E J u s)
    (hg : J.card ≤ paperWidth n) (hH : 3 ≤ H) :
    ∃ t k, k ≤ work time rom n J.card ∧ Block.Eval (Memory.AllData (fun q => ratBits q≤H))
      (block time rom) s k t ∧ Ready D E J u (capacity time rom n) s t := by
  let g := J.card
  let B := capacity time rom n
  let F := slotBase n (g+2)
  let L := live n g
  let r := rank u J.sort
  let m := (if u∈J then 1 else 0 : ℕ)
  let mag := matrixMinorCache D E J u
  let P := fun x => ratBits x≤H
  have hL : 7 ≤ L := (dimensions_le_live n g).2.2
  have gL : g ≤ L := (dimensions_le_live n g).2.1
  have FL : F ≤ L := by dsimp [L,live,F]; omega
  have F7 : 7 ≤ F := by dsimp [F,slotBase,tableBase]; omega
  have rg : r ≤ g := by
    have card : J.sort.length = J.card := @Finset.length_sort _ J _ _ _ _ _
    exact (rank_le_length u J.sort).trans_eq card
  have m1 : m ≤ 1 := by dsimp [m]; split <;> omega
  have cap114 : 114 ≤ B := (capacity_bounds time rom n g hg).1
  obtain ⟨a,ea,ac⟩ := monomialCapacity_spec (fun f : ℕ → ℚ => ∀ j,P (f j)) s 27
    (coefficient time) (exponent time) (rom+114) n ins.dimension ins.persistent.bounds
  have ai (i : ℕ) (hi : i∈controls) : a.index i=s.index i :=
    ac.frame i (control_frames hi).1 (control_frames hi).2.1
  have a7 : a.index 7=L := (ai 7 (by decide)).trans words.free
  obtain ⟨b,eb,stored,bi⟩ := ServiceSave.saveLive_spec P a L hL a7 ea.safe_end
  have bcontrol (i : ℕ) (hi : i∈controls) : b.index i=s.index i :=
    (bi i (control_frames hi).2.2).trans (ai i hi)
  have b27 : b.index 27=B := (bi 27 (by decide)).trans ac.capacity
  have b7 : b.index 7=L := (bcontrol 7 (by decide)).trans words.free
  have b5 : b.index 5=F := (bcontrol 5 (by decide)).trans words.base
  have b17 : b.index 17=g := (bcontrol 17 (by decide)).trans ins.count
  have b22 : b.index 22=n := (bcontrol 22 (by decide)).trans ins.dimension
  have b19 : b.index 19=r := (bcontrol 19 (by decide)).trans ins.rank
  have b1 : b.index 1=m := (bcontrol 1 (by decide)).trans ins.found
  have canClear : 114 ≤ b.index 27 := by rw [b27]; exact cap114
  obtain ⟨c,ec,c0,tab0⟩ := ServiceClean.clearForNumeric_spec P b canClear eb.safe_end hH
  have clean : ServiceClean.Cleaned L F g n r m B b c := by
    simpa only [b7,b5,b17,b22,b19,b1,b27] using c0
  have table : ServiceClean.TableWords (tableBase n) (stride n) (slotBase n g) (slotBase n (g+1)) c := by
    simpa only [bcontrol 14 (by decide),bcontrol 18 (by decide),bcontrol 20 (by decide),bcontrol 21 (by decide),
      ins.base,ins.stride,ins.stop,ins.next] using tab0
  have mult (i : ℕ) (hi : i ≤ g+2) : i*stride n ≤ (g+2)*stride n := Nat.mul_le_mul_right _ hi
  have tableSmall (i : ℕ) (hi : i∈([93,95,97,99] : List ℕ)) : c.index i ≤ L := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · rw [table.baseWord]; dsimp [L,live,slotBase]; omega
    · rw [table.strideWord]
      have h := mult 1 (by omega)
      dsimp [L,live,slotBase] at ⊢
      simp only [one_mul] at h; omega
    · rw [table.stopWord]
      have h := mult g (by omega)
      dsimp [L,live,slotBase]; omega
    · rw [table.nextWord]
      have h := mult (g+1) (by omega)
      dsimp [L,live,slotBase]; omega
  have cb := ServiceFill.oddAddressBudget_of_clear c L F g n r m B clean.metadata FL rg gL m1 tableSmall clean.oddIndex
  have vals (i : Fin (g+1)) : c.data (2*(F+i.val)+1)=mag i := by
    have li : F+i.val < L := by dsimp [L,live,F]; have := i.isLt; omega
    rw [clean.oddData _ (by omega),stored _ (by omega) li (by omega) (by omega),ac.data]
    simpa only [mag,matrixMinorCache,minorMagnitude,evaluatePairMinor_eq,words.base] using words.values i
  obtain ⟨t,et,ready,cost⟩ := ServiceFill.evenInput_spec P c L F g n r m B mag clean.metadata
    FL rg gL m1 clean.evenData clean.evenIndex cb vals ec.safe_end
  have scalarInvariant : (fun m : Memory ℚ => ∀ i, P (m.data i)) = Memory.AllData P := by
    funext m
    rfl
  rw [scalarInvariant] at ea eb ec
  refine ⟨t,_,?_,ea.seq (eb.seq (ec.seq et)),?_,?_,ready.oddAddress,?_,ready.liveWord,ready.rankWord,ready.tableWords table⟩
  · have clearBound := ServiceClean.clearCost_le B
    rw [b27]
    unfold work
    change _ ≤ _+(12*L+28+(10*B+150+40*(n+L+1)))
    omega
  · intro i hi
    exact ready.evenScalar i hi
  · intro i hi
    have flag : (matrixMinorPosition J u).isSome.toNat = m := by
      by_cases present : u ∈ J <;> simp [GeneratorTable.position_present, m, present]
    change t.index (2*i) =
      2*([n,g,(matrixMinorPosition J u).isSome.toNat,r] : List ℕ)[i]?.getD 0
    rw [flag]
    exact ready.evenAddress i hi
  · intro i lo hi i5 i6
    exact (ready.oddScalar i).trans ((clean.oddData i (by omega)).trans
      ((stored _ lo hi i5 i6).trans (congrFun ac.data _)))

end ServicePrepare
end Compression
end LinearProgramming
end Optimization
end OAI
