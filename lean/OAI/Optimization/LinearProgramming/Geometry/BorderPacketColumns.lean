import OAI.Optimization.LinearProgramming.Geometry.BorderMembership

/-! Append the selected columns in canonical increasing order to the minor-request packet. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM RAM.Block

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Programmatic ascending enumeration of the appended column and previous pivot set. -/
def selected (m : Memory K) (v : ℕ) : Bool :=
  decide (m.index 90 = v) || (List.range (m.index 128)).any fun q => m.index (m.index 136+q) = v

def columnNumbers (m : Memory K) (t : ℕ) : List ℕ := (List.range t).filter (selected m)

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem selected_iff (m : Memory K) (v : ℕ) : selected m v = true ↔
    m.index 90 = v ∨ ∃ q < m.index 128, m.index (m.index 136+q) = v := by simp [selected]

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem columnNumbers_succ (m : Memory K) (t : ℕ) : columnNumbers m (t+1) =
    if selected m t then columnNumbers m t ++ [t] else columnNumbers m t := by
  cases h : selected m t <;> simp [columnNumbers,List.range_succ,h]

/-- Store a selected column word and increment both the write pointer and the packet length. -/
def emitColumnWord : Block := .straight [.store 96 30, .incr 96 96, .incr 81 81]

def columnBody : Block := .seq membershipBlock (.seq (.branch (.addrLT 95 94) emitColumnWord .skip)
  (.op (.add 30 30 31)))

def columnsBlock : Block := .seq (.straight [.const 30 0, .const 31 1, .addrConst 95 0])
  (.forRange 91 130 columnBody)

private abbrev Safe (P : K → Prop) (m : Memory K) := ∀ i, P (m.data i)

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem write {P : K → Prop} {m : Memory K} (h : Safe P m) (d : ℕ) {q : K} (hq : P q) :
    Safe P (m.putData d q) := by
  intro i
  by_cases he : i=d
  · simpa [he] using hq
  · simpa [he] using h i

private structure ColumnsInv (m : Memory K) (P : K → Prop) (j : ℕ) (u : Memory K) : Prop where
  safe : Safe P u
  counter : u.index 91=j
  cursor : u.index 96=m.index 96+(columnNumbers m j).length
  length : u.index 81=m.index 81+(columnNumbers m j).length
  zero : u.index 95=0
  numeral : u.data 30=(j : K)
  one : u.data 31=1
  addressFrame (a) : a ≠ 81 → (a < 91 ∨ 97 < a) → u.index a=m.index a
  words (q : ℕ) (hq : q < (columnNumbers m j).length) : u.data (m.index 96+q)=(((columnNumbers m j)[q]?.getD 0 : ℕ) : K)
  scalarFrame (a) : (a < 30 ∨ 31 < a) → (a < m.index 96 ∨ m.index 96+(columnNumbers m j).length ≤ a) → u.data a=m.data a

private theorem emit_eval (P : K → Prop) (u : Memory K) (hu : Safe P u) :
    let u₁ := u.putData (u.index 96) (u.data 30)
    let u₂ := u₁.putIndex 96 (u.index 96+1)
    Eval (Safe P) emitColumnWord u 3 (u₂.putIndex 81 (u.index 81+1)) := by
  dsimp only
  let a := u.putData (u.index 96) (u.data 30)
  let b := a.putIndex 96 (u.index 96+1)
  have h₁ := Eval.op_store (safe := Safe P) u 96 30 hu (write hu _ (hu 30))
  have h₂ : Eval (Safe P) (.op (.incr 96 96)) a 1 b := Eval.op_incr a 96 96 h₁.safe_end h₁.safe_end
  have h₃ : Eval (Safe P) (.op (.incr 81 81)) b 1 (b.putIndex 81 (u.index 81+1)) := by
    simpa [b,a] using Eval.op_incr b 81 81 h₂.safe_end h₂.safe_end
  exact h₁.seq (h₂.seq (h₃.seq (.skip h₃.safe_end)))

private def emitState (u : Memory K) : Memory K :=
  ((u.putData (u.index 96) (u.data 30)).putIndex 96 (u.index 96+1)).putIndex 81 (u.index 81+1)

private theorem column_step (P : K → Prop) (m : Memory K) (hbase : 128 ≤ m.index 136)
    (hptr : 32 ≤ m.index 96) (j : ℕ) (hj : j<m.index 130) (u : Memory K) (h : ColumnsInv m P j u)
    (hnum : ∀ j ≤ m.index 130, P (j : K)) :
    ∃ t k, k ≤ 8*m.index 128+13 ∧ Eval (Safe P) columnBody u k t ∧
      ColumnsInv m P (j+1) (t.putIndex 91 (t.index 91+1)) := by
  classical
  have ui (a : ℕ) (ha : 98≤a) : u.index a=m.index a := h.addressFrame a (by omega) (Or.inr (by omega))
  obtain ⟨b,c,hc,run,bd,flag,bi⟩ := membershipBlock_eval u P h.safe ((ui 136 (by decide)) ▸ hbase)
  have bi' (a : ℕ) (ha : a < 92 ∨ 97 < a) : b.index a=u.index a := bi a (by omega) (by omega) (by omega) (by omega)
  have b81 := bi' 81 (by decide)
  have b91 := (bi' 91 (by decide)).trans h.counter
  have b95 := (bi 95 (by decide) (by decide) (by decide) (by decide)).trans h.zero
  have b96 := (bi 96 (by decide) (by decide) (by decide) (by decide)).trans h.cursor
  have b30 : b.data 30=(j:K) := bd ▸ h.numeral
  have b31 : b.data 31=1 := bd ▸ h.one
  have hseen : seen u (u.index 128) ↔ selected m j := by
    rw [selected_iff]
    unfold seen
    rw [h.addressFrame 90 (by decide) (by decide),h.counter,ui 128 (by decide),ui 136 (by decide)]
    constructor <;> rintro (h' | ⟨q,hq,eq⟩)
    · exact Or.inl h'
    · exact Or.inr ⟨q,hq,(ui _ (by omega)).symm.trans eq⟩
    · exact Or.inl h'
    · exact Or.inr ⟨q,hq,(ui _ (by omega)).trans eq⟩
  let v := if selected m j then emitState b else b
  have branch : ∃ k ≤ 5, Eval (Safe P) (.branch (.addrLT 95 94) emitColumnWord .skip) b k v := by
    cases hg : selected m j with
    | true =>
      have hf : b.index 94=1 := flag.trans (ite_eq_left (hseen.mpr hg))
      refine ⟨5,by decide,?_⟩
      simpa only [v, hg, ↓reduceIte,emitState] using Eval.branchTrue (c := .addrLT 95 94) (b := .skip)
        (by simp [Cond.test,b95,hf]) (emit_eval P b run.safe_end)
    | false =>
      have hf : b.index 94=0 := flag.trans (ite_eq_right (fun h => by have hh := hseen.mp h; simp [hg] at hh))
      refine ⟨1,by decide,?_⟩
      simpa only [v,hg, Bool.false_eq_true, ↓reduceIte] using
        Eval.branchFalse (c := .addrLT 95 94) (a := emitColumnWord) (by simp [Cond.test,b95,hf]) (Eval.skip run.safe_end)
  obtain ⟨d,hd,e⟩ := branch
  have aw : 32 ≤ b.index 96 := b96 ▸ hptr.trans (Nat.le_add_right ..)
  have vd (i : ℕ) (haddr : i≠b.index 96) : v.data i = b.data i := by
    dsimp [v]; split <;> simp [emitState,haddr]
  have vi (i : ℕ) (ha : i≠81) (hb : i≠96) : v.index i=b.index i := by
    dsimp [v]; split <;> simp [emitState,ha,hb]
  have v30 := (vd 30 (by omega)).trans b30
  have v31 := (vd 31 (by omega)).trans b31
  let dst := v.putData 30 (j+1 : ℕ)
  have plus : v.data 30+v.data 31 = ((j+1 : ℕ) : K) := by simp [v30,v31]
  have inc : Eval (Safe P) (.op (.add 30 30 31)) v 1 dst := by
    simpa only [dst,plus] using Eval.op_add v 30 30 31 e.safe_end (write e.safe_end _ (plus.symm ▸ hnum _ hj))
  refine ⟨dst,c+(d+1),by rw [ui 128 (by decide)] at hc; omega,run.seq (e.seq inc),?_⟩
  refine ⟨inc.safe_end,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [dst,vi 91 (by decide) (by decide),b91]
  · cases hg : selected m j <;> simp [dst,v,hg,emitState,columnNumbers_succ,b96,Nat.add_assoc]
  · cases hg : selected m j <;> simp [dst,v,hg,emitState,columnNumbers_succ,b81,h.length,Nat.add_assoc]
  · simp [dst,vi 95 (by decide) (by decide),b95]
  · simp [dst]
  · simpa [dst] using v31
  · intro a a81 ha
    simp [dst,show a ≠ 91 by omega,vi a a81 (by omega),bi' a (by omega),h.addressFrame a a81 ha]
  · intro q hq
    have nonScratch : m.index 96+q ≠ 30 := by omega
    simp only [Memory.putIndex_data, dst, Memory.putData_ne _ nonScratch]
    by_cases hg : selected m j=true
    · have hl : columnNumbers m (j+1) = columnNumbers m j ++ [j] := by simp [columnNumbers_succ,hg]
      rw [hl] at hq ⊢
      have bounds : q ≤ (columnNumbers m j).length := by simpa using hq
      by_cases he : q < (columnNumbers m j).length
      · have neq : m.index 96+q ≠ b.index 96 := by rw [b96]; omega
        simpa [v,hg,emitState,neq,bd,List.getElem?_append_left he] using h.words q he
      · have eq : q=(columnNumbers m j).length := by omega
        simp [v,hg,emitState,b96,b30,eq]
    · have hf : selected m j=false := by simp_all
      have hl : columnNumbers m (j+1) = columnNumbers m j := by simp [columnNumbers_succ,hf]
      rw [hl] at hq ⊢
      simpa [v,hf,bd] using h.words q hq
  · intro p hp hrange
    have neq : p≠30 := by omega
    simp only [Memory.putIndex_data,dst,Memory.putData_ne _ neq]
    cases hg : selected m j with
    | false =>
      simpa [v,hg,bd] using h.scalarFrame p hp (by simpa [columnNumbers_succ,hg] using hrange)
    | true =>
      have hg' : (columnNumbers m (j+1)).length=(columnNumbers m j).length+1 := by simp [columnNumbers_succ,hg]
      have neq' : p ≠ b.index 96 := by rw [b96]; omega
      have out : p < m.index 96 ∨ m.index 96+(columnNumbers m j).length ≤ p := by omega
      simpa [v,hg,emitState,neq',bd] using h.scalarFrame p hp out

/-- Postcondition for appending the ordered column words to an existing packet. -/
structure ColumnOutput (m : Memory K) (t : Memory K) : Prop where
  cursor : t.index 96=m.index 96+(columnNumbers m (m.index 130)).length
  length : t.index 81=m.index 81+(columnNumbers m (m.index 130)).length
  words (q : Fin (columnNumbers m (m.index 130)).length) :
    t.data (m.index 96+q.val)=((columnNumbers m (m.index 130))[q.val] : K)
  scalarFrame (a) : (a < 30 ∨ 31 < a) →
    (a < m.index 96 ∨ m.index 96+(columnNumbers m (m.index 130)).length ≤ a) → t.data a=m.data a
  addressFrame (a) : a ≠ 81 → (a < 91 ∨ 97 < a) → t.index a=m.index a

/-- The executable serialization pass never sorts or enumerates subsets. It scans the
column numbers once and appends exactly those selected by the previous pivot table. -/
theorem columnsBlock_eval (m : Memory K) (P : K → Prop) (hm : ∀ i,P (m.data i))
    (hbase : 128 ≤ m.index 136) (hptr : 32 ≤ m.index 96)
    (hn : ∀ i ≤ m.index 130, P (i : K)) (ho : P 1) :
    ∃ t c, c ≤ m.index 130*(8*m.index 128+16)+5 ∧
      Eval (fun s => ∀ i,P (s.data i)) columnsBlock m c t ∧ ColumnOutput m t := by
  let a := m.putData 30 0
  let b := a.putData 31 1
  let d := b.putIndex 95 0
  have hz : P 0 := by simpa using hn 0 (by omega)
  have za : Eval (Safe P) (.op (.const 30 0)) m 1 a := by
    simpa [a] using Eval.op_const m 30 0 hm (write hm _ (by simpa only [Rat.cast_zero] using hz))
  have ob : Eval (Safe P) (.op (.const 31 1)) a 1 b := by
    simpa [b] using Eval.op_const a 31 1 za.safe_end (write za.safe_end _ (by simpa only [Rat.cast_one] using ho))
  have zd : Eval (Safe P) (.op (.addrConst 95 0)) b 1 d :=
    Eval.op_addrConst b 95 0 ob.safe_end ob.safe_end
  have init : ColumnsInv m P 0 (d.putIndex 91 0) := by
    refine ⟨zd.safe_end,by simp,by simp [d,b,a,columnNumbers],by simp [d,b,a,columnNumbers],
      by simp [d],by simp [d,b,a],by simp [d,b],?_,?_,?_⟩
    · intro u _ hu; simp [d,b,a,show u≠91 by omega,show u≠95 by omega]
    · intro q hq; simp [columnNumbers] at hq
    · intro u hu _; simp [d,b,a,show u≠30 by omega,show u≠31 by omega]
  obtain ⟨t,c,hc,run,out⟩ := Eval.forRange_invariant 91 130 (m.index 130) (8*m.index 128+13)
    (ColumnsInv m P) d zd.safe_end init
    (fun _ _ h => ⟨h.safe,h.counter,h.addressFrame 130 (by decide) (by decide)⟩)
    (fun j hj u h => column_step P m hbase hptr j hj u h hn)
  change c ≤ m.index 130*(8*m.index 128+16)+2 at hc
  refine ⟨t,3+c,by omega,(za.seq (ob.seq (zd.seq (.skip zd.safe_end)))).seq run,
    out.cursor,out.length,?_,out.scalarFrame,out.addressFrame⟩
  intro q
  simpa [List.getElem?_eq_getElem q.isLt] using out.words q.val q.isLt

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
