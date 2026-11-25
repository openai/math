import OAI.Optimization.LinearProgramming.Compression.PhysicalRestartCode
import OAI.Optimization.LinearProgramming.Compression.ServiceCommitGenerator
import OAI.Optimization.LinearProgramming.Compression.ServiceInspected
import OAI.Optimization.LinearProgramming.Compression.ServiceFrame

/-! ## Restoring the physical caller state and inserting a generator at a restart -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM GeneratorTable

variable {d e n : ℕ} {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}

/-- The property of the physical return frame needed by the restart. Only the live
header/matrix/generator prefix and the candidate record are read from the odd scalar bank.
The gap at slot `J.card` and any cells beyond the candidate may hold scratch data. -/
structure RestartSource (J : Finset (NonzeroPairMinor D E)) (q : NonzeroPairMinor D E)
    (old x : Memory ℚ) (live : ℕ) : Prop where
  length : x.index 1=live
  fits : slotBase n (J.card+2)≤live
  rank : x.index 3=GeneratorTable.rank q J.sort
  base : x.index 93=tableBase n
  stride : x.index 95=GeneratorTable.stride n
  stop : x.index 97=slotBase n J.card
  next : x.index 99=slotBase n (J.card+1)
  saved : ∀ i, 1 ≤ i → i<slotBase n J.card → i≠5 → i≠6 → x.data (2*i+1)=old.data i
  candidate : ∀ j<GeneratorTable.stride n, x.data (2*(slotBase n (J.card+1)+j)+1)=old.data (slotBase n (J.card+1)+j)

/-- Direct construction from the physical odd-bank prefix preserved by the inner ROM. -/
theorem RestartSource.of_prefix {J : Finset (NonzeroPairMinor D E)} {q : NonzeroPairMinor D E}
    {old x : Memory ℚ} {live : ℕ} (hlen : x.index 1=live) (fit : slotBase n (J.card+2)≤live)
    (rank : x.index 3=GeneratorTable.rank q J.sort) (base : x.index 93=tableBase n)
    (str : x.index 95=GeneratorTable.stride n) (stop : x.index 97=slotBase n J.card)
    (next : x.index 99=slotBase n (J.card+1))
    (saved : ∀ i, 1 ≤ i → i<live → i≠5 → i≠6 → x.data (2*i+1)=old.data i) :
    RestartSource J q old x live := by
  have last : slotBase n J.card≤slotBase n (J.card+2) :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : J.card≤J.card+2)) _
  refine ⟨hlen,fit,rank,base,str,stop,next,fun i hlo hhi => saved i hlo ((hhi.trans_le last).trans_le fit),?_⟩
  intro j hj
  have high : 7≤slotBase n (J.card+1)+j := by unfold slotBase tableBase; omega
  have inside := slot_word_lt_end n (by omega : J.card+1<J.card+2) hj
  exact saved _ (by omega) (inside.trans_le fit) (by omega) (by omega)

/-- Execute the entire restart continuation through publication of the new count.
`H` bounds the current physical return frame and hence every scalar during this block;
the earlier inspected state can have its own height bound. -/
theorem physicalRestartPost_spec {J : Finset (NonzeroPairMinor D E)} {q : NonzeroPairMinor D E}
    {oldH H live : ℕ} {old x : Memory ℚ} (inspected : Inspected D E J q oldH old)
    (src : RestartSource J q old x live) (fresh : q∉J) (safe : ∀ i,ratBits (x.data i)≤H)
    (one : ratBits (1:ℚ)≤H) (count : ratBits ((J.card+1:ℕ):ℚ)≤H) :
    ∃ t steps, steps≤restartPostBound n J.card live ∧
      Block.Eval (Memory.AllData (fun z => ratBits z≤H)) physicalRestartPost x steps t ∧
      Persistent D E (insert q J) H t ∧ (∀ j<n*n, t.data (7+j)=old.data (7+j)) ∧
      t.index 45=GeneratorTable.rank q J.sort ∧ ∀ i, 40 ≤ i → i≠45 → t.index i=x.index i := by
  let P := fun z : ℚ => ratBits z≤H
  let a := x.putIndex 45 (x.index 3)
  have ea : Block.Eval (Memory.AllData P) (.op (.addrCopy 45 3)) x 1 a := Block.Eval.op_addrCopy _ _ _ safe safe
  obtain ⟨z,ez,_,write,_,zi⟩ := restoreScalarFrameBlock_on a live ea.safe_end (by simpa [a] using src.length)
  let m := applyPlan restartPointers z
  have em : Block.Eval (Memory.AllData P) (addressPlan restartPointers) z 5 m :=
    addressPlan_spec (fun f => ∀ i,P (f i)) _ _ ez.safe_end
  have md : m.data=z.data := applyPlan_data _ _
  have bound : slotBase n J.card≤live := by
    apply le_trans _ src.fits
    exact Nat.add_le_add_left (Nat.mul_le_mul_right (GeneratorTable.stride n) (by omega : J.card≤J.card+2)) _
  have fixed (i : ℕ) (lo : 1 ≤ i) (hi : i<slotBase n J.card) (h5 : i≠5) (h6 : i≠6) :
      m.data i=old.data i := (congrFun md i).trans ((write i lo (hi.trans_le bound) h6).trans (src.saved i lo hi h5 h6))
  have low (i : ℕ) (hi : i≤4) : i<slotBase n J.card := by unfold slotBase tableBase; omega
  have table : Stored D E J.sort m := inspected.persistent.generators.keep_live
    (fixed 4 (by decide) (low 4 (by decide)) (by decide) (by decide))
    (fun i hi hj => fixed i (by omega) (by simpa using hj) (by omega) (by omega))
  have restored : Persistent D E J H m := by
    refine ⟨(fixed 1 (by decide) (low 1 (by decide)) (by decide) (by decide)).trans inspected.persistent.leftRows,
      (fixed 2 (by decide) (low 2 (by decide)) (by decide) (by decide)).trans inspected.persistent.rightRows,
      (fixed 3 (by decide) (low 3 (by decide)) (by decide) (by decide)).trans inspected.persistent.columns,
      ?_,table,em.safe_end⟩
    intro j hj
    exact (fixed (7+j) (by omega) (by unfold slotBase tableBase; omega) (by omega) (by omega)).trans
      (inspected.persistent.entries j hj)
  have staged : SlotAt D E q (slotBase n (J.card+1)) m := by
    apply inspected.candidate.transfer
    intro j hj
    let u := slotBase n (J.card+1)+j
    have u7 : 7≤u := by unfold u slotBase tableBase; omega
    have ulive : u<live := (slot_word_lt_end n (by omega : J.card+1<J.card+2) hj).trans_le src.fits
    exact (congrFun md u).trans ((write u (by omega) ulive (by omega)).trans (src.candidate j hj))
  have z45 : z.index 45=GeneratorTable.rank q J.sort := (zi 45 (by decide) (by decide)).trans
    ((Memory.putIndex_same ..).trans src.rank)
  have zkeep (i : ℕ) (hi : 46 ≤ i) : z.index i=x.index i :=
    (zi i (by omega) (by omega)).trans (Memory.putIndex_ne _ (by omega) _)
  have finalIdx (i : ℕ) (hi : 40 ≤ i) : m.index i=z.index i := by
    simp [m,restartPointers,applyPlan,AddressSet.apply,show i≠14 by omega,show i≠18 by omega,
      show i≠19 by omega,show i≠20 by omega,show i≠21 by omega]
  obtain ⟨t,k,hk,run,done,ik,_⟩ := restored.commitGenerator q fresh staged
    (by simp [m,restartPointers,applyPlan,AddressSet.apply,zkeep 93 (by decide),src.base])
    (by simp [m,restartPointers,applyPlan,AddressSet.apply,zkeep 95 (by decide),src.stride])
    (by simp [m,restartPointers,applyPlan,AddressSet.apply,z45])
    (by simp [m,restartPointers,applyPlan,AddressSet.apply,zkeep 97 (by decide),src.stop])
    (by simp [m,restartPointers,applyPlan,AddressSet.apply,zkeep 99 (by decide),src.next]) one count
  refine ⟨t,1+((7*(live-1)+3)+(5+k)),by unfold restartPostBound; omega,
    ea.seq (ez.seq (em.seq run)),done,fun j hj => (done.entries j hj).trans (inspected.persistent.entries j hj).symm,
    (ik 45 (by decide)).trans ((finalIdx 45 (by decide)).trans z45),?_⟩
  intro i hi h45
  exact (ik i hi).trans ((finalIdx i hi).trans ((zi i (by omega) (by omega)).trans (Memory.putIndex_ne _ h45 _)))

end Compression
end LinearProgramming
end Optimization
end OAI
