import OAI.Optimization.LinearProgramming.Geometry.RawLabelLayout
import OAI.Optimization.LinearProgramming.Geometry.RawLabelCopy
import OAI.Optimization.LinearProgramming.Geometry.RawLabelTape

/-! Execute the raw scalar-tape placement before the relocatable geometric header call. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace LabelInput

open RAM Matrix
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {r s n : ℕ}

def placeInputs : Block := .seq rawAddresses (.seq copyRaw copyDual)

theorem placeInputs_spec (P : K → Prop) (m : Memory K) (hm : m.AllData P)
    (D : Matrix (Fin r) (Fin n) K) (E : Matrix (Fin s) (Fin n) K) (p : Fin n → K) (i : Fin n)
    (hr : m.index 0=r) (hs : m.index 1=s) (hn : m.index 2=n) (hi : m.index 3=i.val)
    (hD : ∀ a : Fin r, ∀ b : Fin n, m.data (a.val*n+b.val)=D a b)
    (hE : ∀ a : Fin s, ∀ b : Fin n, m.data (r*n+(a.val*n+b.val))=E a b)
    (hp : ∀ b : Fin n, m.data (r*n+(s*n+b.val))=p b) :
    let x := standardBuffers r s n
    ∃ t c, c ≤ 4100*(r+s+n+1)^2 ∧ Block.Eval (Memory.AllData P) placeInputs m c t ∧
      Inputs x D E p i t ∧ (∀ a, a≠0 → (a<x.dual ∨ x.free≤a) → t.data a=m.data a) ∧
      ∀ a, 256≤a → t.index a=m.index a := by
  let x := standardBuffers r s n
  let len := rawSize r s n
  change ∃ (t : Memory K) (c : ℕ), c ≤ 4100*(r+s+n+1)^2 ∧
    Block.Eval (Memory.AllData P) placeInputs m c t ∧ Inputs x D E p i t ∧ _
  have L : len=r*n+s*n+n := rfl
  have db : x.dual=256+len := rfl
  have pb : x.primal=x.dual+s*n := rfl
  have tb : x.price=x.primal+r*n+s*n := rfl
  have fb : x.free=x.price+n := rfl
  have positive := i.isLt
  obtain ⟨a,c,ca,ea,ha,da,fa⟩ := rawAddresses_spec P m hm r s n i.val hr hs hn hi
  obtain ⟨b,eb,hb⟩ := copyRaw_spec P a ea.safe_end x.primal len ha.primal ha.total (by omega) (by omega)
  have ab (w : ℕ) (hw : 200≤w) := hb.indexFrame w (by omega) (by omega) (by omega) (by omega)
  have positions := ha.of_frame ab
  obtain ⟨t,et,ht⟩ := copyDual_spec P b eb.safe_end (x.primal+r*n) x.dual (s*n) positions.dualSource
    positions.dual positions.dualLength (by omega) (by omega)
  have bt (w : ℕ) (hw : 200≤w) := ht.indexFrame w (by omega) (by omega) (by omega) (by omega)
  have final := positions.of_frame bt
  have raw (j : ℕ) (hj : j<len) : b.data (x.primal+j)=m.data j := by
    rw [hb.words j hj,Nat.zero_add,da]
  have same (j : ℕ) : t.data (x.primal+j)=b.data (x.primal+j) := ht.dataFrame _ (by omega) (Or.inr (by omega))
  have prepared : Inputs x D E p i t := by
    refine ⟨final.dual,final.indices,final.rank,final.dualRank,final.columns,final.designated,
      final.primal,final.prices,final.free,?_,?_,?_⟩
    · intro u v
      have uv := matrixWord_lt u v
      rw [Nat.add_assoc,same,raw _ (by omega),hD]
    · intro u v
      have uv := matrixWord_lt u v
      rw [Nat.add_assoc,ht.words _ uv,Nat.add_assoc,raw _ (by omega),hE]
    · intro v
      have vv := v.isLt
      rw [tb,Nat.add_assoc,Nat.add_assoc,same,raw _ (by omega),hp]
  refine ⟨t,_,?_,ea.seq (eb.seq et),prepared,?_,?_⟩
  · have hlt := Nat.sub_le len 1
    change c+(7*(len-1)+6+(7*(s*n)+5)) ≤ _
    have upper : c+(7*(len-1)+6+(7*(s*n)+5)) ≤ 4000*(r+s+n+1)^2 + (7*len+6+(7*(s*n)+5)) := by omega
    apply upper.trans
    rw [L]
    ring_nf
    omega
  · intro j hj hoff
    change j<x.dual ∨ x.free≤j at hoff
    rw [ht.dataFrame j hj (by omega),hb.dataFrame j hj (by omega),da]
  · intro j hj
    rw [bt _ (by omega),ab _ (by omega),fa _ hj]

end LabelInput
end Geometry
end LinearProgramming
end Optimization
end OAI
