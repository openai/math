import OAI.Optimization.LinearProgramming.Geometry.UniformCopyTable
import OAI.Optimization.LinearProgramming.Geometry.UniformGramLayout
import OAI.Optimization.LinearProgramming.Compression.UniformDetFrame

/-! The fixed cofactor callback for the Gram inverse. It nests a row-substituted
table construction and one uniform Bird determinant inside the outer table loop. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM Compression

def CofactorKeep (p : ℕ) : Prop :=
  p=0 ∨ p=1 ∨ p=11 ∨ p=12 ∨ p=14 ∨ p=40 ∨ p=41 ∨ 50 ≤ p
instance (p : ℕ) : Decidable (CofactorKeep p) := by unfold CofactorKeep; infer_instance

def saveCofactorIndices : List (ℕ × ℕ) := [(44,30),(43,32),(45,35),(35,58)]
def restoreCofactorIndices : List (ℕ × ℕ) := [(30,44),(32,43),(35,45)]

def uniformCofactorCell : Block :=
  .seq (indexMoves saveCofactorIndices)
    (.seq (uniformTableBlock GramCopy.cofactorCell)
      (.seq (uniformDetBlock uniformBirdCell)
        (.seq (.op (.mul 6 15 6)) (indexMoves restoreCofactorIndices))))

def uniformCofactorTime (r : ℕ) := 8 + uniformTableTime r r (r*(4*r+5)+4*r+12) + 2000*(r+1)^7

theorem gramUpdateRow_coordinates {K : Type} [Field K] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) K) (i j p q : Fin r) :
    (if p.val = j.val then (if q.val = i.val then 1 else 0) else G p q) =
      (G.updateRow j (Pi.single i 1)) p q := by
  by_cases hp : p = j
  · subst p; by_cases hq : q=i
    · subst q; simp
    · have hn : q.val≠i.val := fun e => hq (Fin.ext e)
      simp [hn,hq]
  · have hn : p.val≠j.val := fun e => hp (Fin.ext e)
    simp [hn,hp]

private def InnerCopyKeep (p : ℕ) : Prop := ¬TableScratch p ∧ p ≠ 38 ∧ p ≠ 39 ∧ p ≠ 42
private instance (p : ℕ) : Decidable (InnerCopyKeep p) := by unfold InnerCopyKeep; infer_instance

/-- One outer callback computes one inverse entry. It restores the two outer
loop counters and output base after the nested table traversal. -/
theorem uniformCofactorCell_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (r g inv sub wa wb : ℕ) (i j : Fin r)
    (h0 : s.index 0=r) (h1 : s.index 1=sub) (h11 : s.index 11=wa) (h12 : s.index 12=wb)
    (h14 : s.index 14=0) (h30 : s.index 30=i.val) (h31 : s.index 31=r)
    (h32 : s.index 32=j.val) (h33 : s.index 33=r) (h35 : s.index 35=inv)
    (h40 : s.index 40=g) (h41 : s.index 41=r) (h58 : s.index 58=sub)
    (hg : 64 ≤ g) (hgi : g+r*r ≤ inv) (his : inv+r*r ≤ sub)
    (hsa : sub+r*r ≤ wa) (hab : wa+r*r ≤ wb)
    (hs : s.AllData P) (hp0 : P 0) (hp1 : P 1) (hpneg : ∀ x, P x → P (-x))
    (hbird : ∀ k < r, ∀ z : BirdRegister r,
      let A := (uniformRect r r g s).updateRow j (Pi.single i 1)
      P (z.read A (birdLayer A k)))
    (hscaled : P (s.data 15 * ((uniformRect r r g s).updateRow j (Pi.single i 1)).det)) :
    ∃ t cost, cost ≤ uniformCofactorTime r ∧ Block.Eval (Memory.AllData P) uniformCofactorCell s cost t ∧
      t.data 6 = s.data 15 * ((uniformRect r r g s).updateRow j (Pi.single i 1)).det ∧
      (∀ p, 7 ≤ p → (p < sub ∨ wb+r*r ≤ p) → t.data p=s.data p) ∧
      ∀ p, TableControl p ∨ CofactorKeep p → t.index p=s.index p := by
  let u := movedIndices s saveCofactorIndices
  let A := (uniformRect r r g s).updateRow j (Pi.single i 1)
  have eu : Block.Eval (Memory.AllData P) (indexMoves saveCofactorIndices) s 4 u :=
    indexMoves_eval P s hs _
  have uf (p : ℕ) (h35 : p≠35) (h43 : p≠43) (h44 : p≠44) (h45 : p≠45) :
      u.index p = s.index p := by
    apply movedIndices_other
    simp [saveCofactorIndices,h35,h43,h44,h45]
  have u35 : u.index 35=sub := by simpa [u,saveCofactorIndices,movedIndices] using h58
  have u43 : u.index 43=j.val := by simpa [u,saveCofactorIndices,movedIndices] using h32
  have u44 : u.index 44=i.val := by simpa [u,saveCofactorIndices,movedIndices] using h30
  have u45 : u.index 45=inv := by simpa [u,saveCofactorIndices,movedIndices] using h35
  have u40 := (uf 40 (by decide) (by decide) (by decide) (by decide)).trans h40
  have u41 := (uf 41 (by decide) (by decide) (by decide) (by decide)).trans h41
  let target : Matrix (Fin r) (Fin r) K := fun p q =>
    if p.val = u.index 43 then (if q.val=u.index 44 then 1 else 0)
    else u.data (u.index 40+p.val*r+q.val)
  have etarget : target = A := by
    ext p q
    simpa only [target, u43, u44, u40, u, movedIndices_data, A, uniformRect] using
      gramUpdateRow_coordinates (uniformRect r r g s) i j p q
  have cb : TableCallbackSpec GramCopy.cofactorCell P (fun z => 7 ≤ z) InnerCopyKeep
      u r r sub target (r*(4*r+5)+4*r+12) := by
    apply GramCopy.cofactor_callback P (fun z => 7 ≤ z) InnerCopyKeep u r sub u41 hp0 hp1
      (by decide) (fun p hp => hp.2) (by decide) (by decide) (by decide) (by decide)
    intro p q
    have hpos := rectOffset_lt p q
    rw [u40]
    omega
  obtain ⟨v,c,hc,eCopy,vTable,vData,vIdx⟩ := uniformTableBlock_spec GramCopy.cofactorCell P
    (fun q => 7 ≤ q) InnerCopyKeep u r r sub target (r*(4*r+5)+4*r+12) cb
    (fun p hp => hp.1) (fun p q => by omega)
    ((uf 31 (by decide) (by decide) (by decide) (by decide)).trans h31)
    ((uf 33 (by decide) (by decide) (by decide) (by decide)).trans h33) u35 eu.safe_end
  rw [etarget] at vTable
  have vf (p : ℕ) (hp : InnerCopyKeep p) : v.index p = u.index p := vIdx p (Or.inr hp)
  have v0 := ((vf 0 (by decide)).trans (uf 0 (by decide) (by decide) (by decide) (by decide))).trans h0
  have v1 := ((vf 1 (by decide)).trans (uf 1 (by decide) (by decide) (by decide) (by decide))).trans h1
  have v11 := ((vf 11 (by decide)).trans (uf 11 (by decide) (by decide) (by decide) (by decide))).trans h11
  have v12 := ((vf 12 (by decide)).trans (uf 12 (by decide) (by decide) (by decide) (by decide))).trans h12
  have v14 := ((vf 14 (by decide)).trans (uf 14 (by decide) (by decide) (by decide) (by decide))).trans h14
  have vA : uniformMatrix r (v.index 1) v = A := by rw [v1]; exact vTable
  obtain ⟨w,k,hk,eDet,w6,wData⟩ := uniformDetBlock_spec uniformBirdCell uniformBirdCell_spec P v r
    v0 (v1 ▸ by omega) (by rw [v1,v11]; exact hsa) (by rw [v11,v12]; exact hab)
    v14 eCopy.safe_end hp0 hp1 hpneg (by rw [vA]; exact hbird)
  rw [vA] at w6
  have wf (q : ℕ) (hq : q ∉ ({2,3,4,5,6,7,8,9,10,13} : Finset ℕ)) :=
    uniformDet_address_frame eDet q hq
  have scalarFrame (q : ℕ) (hq : 7 ≤ q) (hq' : q < sub ∨ wb+r*r ≤ q) : w.data q=s.data q := by
    rw [wData q hq (by rw [v11]; omega) (by rw [v12]; omega),
      vData q hq (by omega)]
    exact congrFun (movedIndices_data s saveCofactorIndices) q
  have w15 := scalarFrame 15 (by decide) (Or.inl (by omega))
  let z := w.putData 6 (w.data 15 * w.data 6)
  have eMul : Block.Eval (Memory.AllData P) (.op (.mul 6 15 6)) w 1 z :=
    Block.Eval.op_mul _ _ _ _ eDet.safe_end (Memory.AllData.putData (P := P) eDet.safe_end _
      (by rw [w15,w6]; exact hscaled))
  let t := movedIndices z restoreCofactorIndices
  have eRestore : Block.Eval (Memory.AllData P) (indexMoves restoreCofactorIndices) z 3 t :=
    indexMoves_eval P z eMul.safe_end _
  have w43 := ((wf 43 (by decide)).trans (vf 43 (by decide))).trans u43
  have w44 := ((wf 44 (by decide)).trans (vf 44 (by decide))).trans u44
  have w45 := ((wf 45 (by decide)).trans (vf 45 (by decide))).trans u45
  refine ⟨t,_,?_,eu.seq (eCopy.seq (eDet.seq (eMul.seq eRestore))),?_,?_,?_⟩
  · unfold uniformCofactorTime; omega
  · simp [t,z,w6,w15,A]
  · intro q hq hq'
    simpa [t,z,show q ≠ 6 by omega] using scalarFrame q hq hq'
  · intro q hq
    by_cases hq30 : q=30
    · subst q; simpa [t,z,restoreCofactorIndices,movedIndices,h30] using w44
    by_cases hq32 : q=32
    · subst q; simpa [t,z,restoreCofactorIndices,movedIndices,h32] using w43
    by_cases hq35 : q=35
    · subst q; simpa [t,z,restoreCofactorIndices,movedIndices,h35] using w45
    have hrs : ∀ v ∈ restoreCofactorIndices, q≠v.1 := by simp [restoreCofactorIndices,hq30,hq32,hq35]
    have hbase : TableControl q ∨ CofactorKeep q := hq
    simp only [TableControl,CofactorKeep] at hbase
    have hdet : q ∉ ({2,3,4,5,6,7,8,9,10,13} : Finset ℕ) := by simp only [Finset.mem_insert,Finset.mem_singleton]; omega
    have hcp : InnerCopyKeep q := by dsimp [InnerCopyKeep,TableScratch]; omega
    exact (movedIndices_other z restoreCofactorIndices q hrs).trans
      ((wf q hdet).trans ((vf q hcp).trans (uf q hq35 (by omega) (by omega) (by omega))))

/-- The same two loops emit all r² inverse entries for every input. -/
def uniformInverseTable : Block := uniformTableBlock uniformCofactorCell

theorem uniformInverseTable_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (r g inv sub wa wb : ℕ)
    (h0 : s.index 0=r) (h1 : s.index 1=sub) (h11 : s.index 11=wa) (h12 : s.index 12=wb)
    (h14 : s.index 14=0) (h31 : s.index 31=r) (h33 : s.index 33=r) (h35 : s.index 35=inv)
    (h40 : s.index 40=g) (h41 : s.index 41=r) (h58 : s.index 58=sub)
    (hg : 64 ≤ g) (hgi : g+r*r ≤ inv) (his : inv+r*r ≤ sub) (hsa : sub+r*r ≤ wa) (hab : wa+r*r ≤ wb)
    (hs : s.AllData P) (hp0 : P 0) (hp1 : P 1) (hpneg : ∀ x, P x → P (-x))
    (hrec : s.data 15 = (uniformRect r r g s).det⁻¹)
    (hbird : ∀ (i j : Fin r) k, k < r → ∀ z : BirdRegister r,
      let A := (uniformRect r r g s).updateRow j (Pi.single i 1)
      P (z.read A (birdLayer A k)))
    (hscaled : ∀ i j : Fin r, P (s.data 15 * ((uniformRect r r g s).updateRow j (Pi.single i 1)).det)) :
    ∃ t cost, cost ≤ uniformTableTime r r (uniformCofactorTime r) ∧
      Block.Eval (Memory.AllData P) uniformInverseTable s cost t ∧
      uniformRect r r inv t=(uniformRect r r g s)⁻¹ ∧
      (∀ p, 7 ≤ p → (p < sub ∨ wb+r*r ≤ p) → (p < inv ∨ inv+r*r ≤ p) → t.data p=s.data p) ∧
      ∀ p, CofactorKeep p → t.index p=s.index p := by
  let care := fun q : ℕ => 7 ≤ q ∧ (q < sub ∨ wb+r*r ≤ q)
  let G := uniformRect r r g s
  have hc : TableCallbackSpec uniformCofactorCell P care CofactorKeep s r r inv G⁻¹
      (uniformCofactorTime r) := by
    intro i j u hu hi hj hf hm
    have hG : uniformRect r r g u = G := by
      ext a b
      have h := rectOffset_lt a b
      exact hm _ ⟨by omega,Or.inl (by omega)⟩ (Or.inl (by omega))
    have h15 : u.data 15 = s.data 15 := hm 15 ⟨by decide,Or.inl (by omega)⟩ (Or.inl (by omega))
    obtain ⟨t,k,hk,he,hv,hd,hidx⟩ := uniformCofactorCell_spec P u r g inv sub wa wb i j
      ((hf 0 (Or.inr (by decide))).trans h0) ((hf 1 (Or.inr (by decide))).trans h1)
      ((hf 11 (Or.inr (by decide))).trans h11) ((hf 12 (Or.inr (by decide))).trans h12)
      ((hf 14 (Or.inr (by decide))).trans h14) hi ((hf 31 (Or.inl (by decide))).trans h31)
      hj ((hf 33 (Or.inl (by decide))).trans h33) ((hf 35 (Or.inl (by decide))).trans h35)
      ((hf 40 (Or.inr (by decide))).trans h40) ((hf 41 (Or.inr (by decide))).trans h41)
      ((hf 58 (Or.inr (by decide))).trans h58) hg hgi his hsa hab hu hp0 hp1 hpneg
      (by rw [hG]; exact hbird i j) (by rw [hG,h15]; exact hscaled i j)
    rw [h15,hrec,hG] at hv
    refine ⟨t,k,hk,he,hv.trans ?_,fun p hp => hd p hp.1 hp.2,hidx⟩
    simp [G,Matrix.inv_def,Ring.inverse_eq_inv,Matrix.adjugate_apply]
  have hprot (p : ℕ) (hp : CofactorKeep p) : ¬TableScratch p := by
    unfold CofactorKeep at hp; unfold TableScratch; omega
  have harea (i j : Fin r) : care (inv+i.val*r+j.val) := by
    have h := rectOffset_lt i j
    exact ⟨by omega,Or.inl (by omega)⟩
  obtain ⟨t,k,hk,he,hv,hd,hi⟩ := uniformTableBlock_spec uniformCofactorCell P care CofactorKeep
    s r r inv G⁻¹ _ hc hprot harea h31 h33 h35 hs
  exact ⟨t,k,hk,he,hv,fun p h₁ h₂ h₃ => hd p ⟨h₁,h₂⟩ h₃,fun p hp => hi p (Or.inr hp)⟩

end Geometry
end LinearProgramming
end Optimization
end OAI
