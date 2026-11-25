import OAI.Optimization.LinearProgramming.Compression.ServiceInspectProgram
import OAI.Optimization.LinearProgramming.Compression.ServiceCanonicalIndex
import OAI.Optimization.LinearProgramming.Compression.MinorDetBounds
import OAI.Optimization.LinearProgramming.Compression.ServiceCandidateDet
import OAI.Optimization.LinearProgramming.Compression.ServiceGeneratorLookup
import OAI.Optimization.LinearProgramming.Compression.ServiceIngress
import OAI.Optimization.LinearProgramming.Compression.ServiceInspected

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM OracleSpec

private theorem ingress_wire {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (u : MinorLog.Index D E) (P : ℚ→Prop) (s : State ℚ)
    (hs : s.memory.AllData P) (hsum : s.data 3 = s.data 1+s.data 2) (hone : P 1) (hv : ∀ j ≤ n,P (j:ℚ)) :
    let q := MinorLog.indexEquiv D E u
    let m := (MinorLog.resume s (MinorLog.words u.val)).memory
    ∃t,Block.Eval (Memory.AllData P) Ingress.stageRequest m (Ingress.stageCost (order q.val)) t ∧
      Wire q.val t ∧ ∀ j,j ≠ 0 → j ≠ 5 → j ≠ 6 → t.data j = s.data j := by
  let q := MinorLog.indexEquiv D E u
  let m := (MinorLog.resume s (MinorLog.words u.val)).memory
  have eq : MinorLog.words u.val = publicWords q.val := (publicWords_of_index D E u).symm
  have zero : m.index 0 = tag q.val := by simp [m,MinorLog.resume,State.memory,eq,publicWords]
  have one : m.index 1 = order q.val := by simp [m,MinorLog.resume,State.memory,eq,publicWords]
  obtain ⟨t,et,buf,fr⟩ := Ingress.stageRequest_spec P m (tag q.val) (order q.val) (tag_le _) zero one
    hsum hs hone (fun j hj => hv j (hj.trans (order_le _)))
  refine ⟨t,et,Wire.of_canonical (buf.base ▸ (by omega)) buf.side buf.order ?_,fr⟩
  intro j hj
  have len : j < (publicWords q.val).length := by rw [publicWords_length]; exact hj
  rw [buf.base,buf.word j hj]
  change (MinorLog.words u.val)[j]?.getD (s.index j) = (publicWords q.val)[j]?.getD 0
  rw [eq, List.getElem?_eq_getElem len]
  simp only [Option.getD_some]

private theorem natBits_le (j : ℕ) : ratBits (j:ℚ) ≤ j+3 := by
  simp only [ratBits,Rat.num_natCast,Int.natAbs_natCast,Rat.den_natCast,
    show Nat.log2 1 = 0 by rfl,Nat.add_zero]
  have hj := Nat.log2_le_self j
  omega

/-- A real request may overwrite the previous low addresses. This fixed procedure retains
all original matrix and generator values while recovering the exact sorted rank and membership. -/
theorem inspectRequest_spec (cmp : Block) (C : ℕ→ℕ) (hcmp : SlotComparatorSpec cmp C) (hC : ∀ n,C n ≤ 100*(n+1))
    {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (J : Finset (NonzeroPairMinor D E)) (H : ℕ) (s : State ℚ) (u : MinorLog.Index D E)
    (hdim : d+e = n) (persist : Persistent D E J H s.memory)
    (hheight : 40*(matrixEncodingLength D+matrixEncodingLength E+1)^4 ≤ H)
    (hsmall : 3+max (4*(n+1)^2) (J.card+1) ≤ H) :
    ∃t l,l ≤ 3000*(J.card+1)*(n+1)^7 ∧ Block.Eval (Memory.AllData (fun r => ratBits r ≤ H))
      (inspectRequest cmp) (MinorLog.resume s (MinorLog.words u.val)).memory l t ∧
      Inspected D E J (MinorLog.indexEquiv D E u) H t := by
  let P := fun x : ℚ => ratBits x ≤ H
  let q := MinorLog.indexEquiv D E u
  let keys := J.sort
  have len : keys.length = J.card := by simp [keys]
  let N := max (4*(n+1)^2) (J.card+1)
  have hn : n ≤ 4*(n+1)^2 := by ring_nf; omega
  have hn' : n ≤ N := hn.trans (le_max_left _ _)
  have hg : keys.length ≤ N := len ▸ (Nat.le_succ _ |>.trans (le_max_right _ _))
  have hv (j : ℕ) (hj : j ≤ N) : P (j:ℚ) := (natBits_le j).trans (by dsimp [N] at hj;omega)
  have hz : P 0 := by simpa using hv 0 (Nat.zero_le _)
  have b1 : 1 ≤ N := (show 1 ≤ 4*(n+1)^2 by ring_nf;omega).trans (le_max_left _ _)
  have one : P 1 := by simpa using hv 1 b1
  have neg (x : ℚ) (hx : P x) : P (-x) := by simpa [P,ratBits] using hx
  have ssum : s.data 3 = s.data 1+s.data 2 := by
    rw [show s.data 3 = (n:ℚ) from persist.columns,show s.data 1 = (d:ℚ) from persist.leftRows,
      show s.data 2 = (e:ℚ) from persist.rightRows,← Nat.cast_add,hdim]
  obtain ⟨a,ea,wa,af⟩ := ingress_wire D E u P s persist.bounds ssum one (fun j hj => hv j (hj.trans hn'))
  have pa := persist.keep af ea.safe_end
  obtain ⟨_,_,_,_,_,bird⟩ := MinorLoad.rationalPairRegisterBounds D E q.val hdim
  obtain ⟨b,k,hk,eb,cand⟩ := candidateDet_spec D E q.val keys.length P a hdim pa.leftRows pa.columns pa.generators.count
    (MatrixBank.of_public D E a hdim pa.entries) wa ea.safe_end hz one neg (fun j hj => hv j (hj.trans (max_le hn' hg)))
    (fun j hj r => (bird j hj r).trans hheight)
  have btable := cand.table pa.generators
  have b3 := (cand.header 3 (by decide) (by decide)).trans pa.columns
  obtain ⟨t,l,hl,et,loc⟩ := lookup_spec cmp C hcmp D E keys q P b hdim btable b3 (wa.frame cand.indices) cand.magnitude
    eb.safe_end (fun j hj => hv j (by simpa only [len] using hj))
  have lookupSafe : (fun m : Memory ℚ => ∀ i, P (m.data i)) = Memory.AllData P := by
    funext m
    rfl
  rw [lookupSafe] at et
  have kept (i : ℕ) (lo : 1 ≤ i) (hi : i ≤ 3) : t.data i = a.data i :=
    (loc.data i (by omega) (by omega) (by omega) (by unfold tableBase;omega)).trans (cand.header i lo (by omega))
  have pt : Persistent D E J H t := ⟨(kept 1 (by decide) (by decide)).trans pa.leftRows,
    (kept 2 (by decide) (by decide)).trans pa.rightRows,(kept 3 (by decide) (by decide)).trans pa.columns,
    fun j hj => (loc.data _ (by omega) (by omega) (by omega) (by unfold tableBase; omega)).trans
      ((cand.data _ (by omega) (by unfold slotBase tableBase;omega)).trans (pa.entries j hj)),loc.table,et.safe_end⟩
  have en := Ingress.stageCost_le (order q.val)
  have eu := order_le q.val
  have cp := prepareCost_le n keys.length
  have ch := Nat.mul_le_mul_left keys.length (Nat.add_le_add_right (hC n) (4*stride n+12))
  have lookupBound : l ≤ 100*(keys.length+1)*(n+1)^2+40*(n+1)^2+keys.length*(100*(n+1)+4*stride n+12)+1 := by
    unfold lookupCost at hl
    simp only [Nat.add_assoc] at hl ch ⊢
    omega
  have cost : Ingress.stageCost (order q.val)+(k+l) ≤ 3000*(J.card+1)*(n+1)^7 := calc
    _ ≤(22*n+166)+(2500*(J.card+1)*(n+1)^7+
      (100*(J.card+1)*(n+1)^2+40*(n+1)^2+J.card*(100*(n+1)+4*stride n+12)+1)) := by rw [len] at hk lookupBound;omega
    _ ≤_ := by unfold stride; ring_nf;omega
  exact ⟨t,_,cost,ea.seq (eb.seq et),pt,by simpa only [len] using loc.request,loc.rank,
    by simpa [keys] using loc.found,loc.base,loc.count.trans len,loc.width,by simpa only [len] using loc.stop,
    by simpa only [len] using loc.incoming,loc.dimension⟩

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
