import OAI.Hierarchy.DescentResetTrunkScalar
import OAI.Hierarchy.DescentResetStemHeaders

namespace OAI
/-! # The predecessor trunk flag from the shared scalar header and original lane mask -/
namespace Hierarchy.DescentRetainedHubFlag
open DescentPackedColony DescentSIMDLookup DescentPackedZip DescentDyadicSpan DescentResetStemHeaders DescentResetFieldAssembler
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

def flagWord (b M used : ℕ) : Cell (b*M):=encode b M (fun j=>if j.val<used then 1 else 0)

def hub (H G M «meta» b scalar hdr : ℕ) : Expr :=
  let a:=«meta»*7
  let n:=H*chunks G M
  let field:Expr:=.lookup (rawBank scalar H 0) (.lookup (actorBank hdr a n) .row)
  let mask:Expr:=.lookup (maskBank hdr a n) .row
  .branch .lt field (.lit (2^(«meta»*5)))
    (.branch .eq mask (.lit (2^(a*M)-1)) (.lit (flagWord b M M).val) (.lit (flagWord b M (G%M)).val)) (.lit 0)

theorem work (H G M «meta» b scalar hdr : ℕ): (hub H G M «meta» b scalar hdr).work=26:=rfl

private theorem chunk_tail {G M : ℕ} (positive : 0<M) (p : Fin (chunks G M)) (short_ : used G M p.val<M) :
    used G M p.val=G%M:=by
  have jj : p.val+1≤(G+M-1)/M:=p.isLt
  have offset := (Nat.le_div_iff_mul_le positive).1 jj
  rw [Nat.add_mul,Nat.one_mul] at offset
  have le:p.val*M≤G:=by omega
  have low:G-p.val*M<M:=by
    change min M (G-p.val*M)<M at short_
    omega
  rw [used,min_eq_right low.le]
  have recover:=Nat.sub_add_cancel le
  calc G-p.val*M = (G-p.val*M)%M :=(Nat.mod_eq_of_lt low).symm
       _ = (G-p.val*M+p.val*M)%M :=by simp
       _ = G%M :=congrArg (·%M) recover

private theorem data_ones {H G M b : ℕ} (p : Row H G M) :
    data (fun (_:Fin H) (_:Fin G)=>(1:Cell b)) p=flagWord b M (used G M p.2.val):=by
  apply congrArg (encode b M)
  funext i
  have test : p.2.val*M+i.val<G ↔ i.val<used G M p.2.val:=by
    refine ⟨active i,fun h=>?_⟩
    have hi: i.val<G-p.2.val*M:=(lt_min_iff.mp h).2
    omega
  by_cases live : p.2.val*M+i.val<G
  · simp [live,test.mp live]
  · have outside : ¬ i.val < used G M p.2.val := fun h => live (test.mpr h)
    simp [live,outside]

private theorem core_order {«meta» : ℕ} (pos : 0<«meta») (m : Meta) (z : m.units=0) :
    (raw «meta» m).val<2^(«meta»*5) ↔ m.core=false:=by
  let n:=(raw «meta» m).val
  have high: n<2^(«meta»*7):=(raw «meta» m).isLt
  have finalDigit:digit «meta» 6 n=0:=by
    have digit₀:=digit_encode (fun j=>(digits m j:Cell «meta»)) (6:Fin 7)
    simpa [n,raw,digits,z] using digit₀
  have end_ : n<2^(«meta»*6):=by
    apply Nat.lt_of_div_eq_zero (Nat.two_pow_pos _)
    simpa [digit,Nat.mod_eq_of_lt high] using finalDigit
  have nextDigit:digit «meta» 5 n=m.core.toNat:=by
    have digit₀:=digit_encode (fun j=>(digits m j:Cell «meta»)) (5:Fin 7)
    have small:m.core.toNat<2^«meta»:=by
      have two : 2≤2^«meta»:=by simpa using Nat.pow_le_pow_right (by decide:0<2) pos
      cases m.core with
      | false => exact Nat.two_pow_pos _
      | true => exact two
    simpa [n,raw,digits,Fin.val_cast_of_lt small] using digit₀
  have div : n/2^(«meta»*5)=m.core.toNat:=by simpa [digit,Nat.mod_eq_of_lt end_] using nextDigit
  change n<2^(«meta»*5) ↔ _
  rw [←Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _),div]
  cases m.core <;> decide

theorem ready {H G M «meta» b scalar hdr w limit : ℕ}
    (fit : (body H G M («meta»*7) scalar hdr 0).Fits w limit) :
    (hub H G M «meta» b scalar hdr).Fits w limit:=
  ⟨fit.1.2,trivial,⟨fit.2,trivial,trivial,trivial⟩,trivial⟩

theorem source {H G M «meta» b scalar hdr w limit : ℕ} (pM : 0<M) (pMeta : 0<«meta»)
    (wide : «meta»*7*M≤w) (_outFit : b*M≤w)
    (records : Fin H→Meta) (units : ∀h,(records h).units=0)
    (m : Memory w) (stored : TablesOK H G M («meta»*7) hdr m)
    (field : ∀h : Fin H,m (scalar+h.val)=((raw «meta» (records h)).val:Word w))
    (safe : (body H G M («meta»*7) scalar hdr 0).Fits w limit) :
    Source (hub H G M «meta» b scalar hdr) (fun h (_:Fin G)=>if (records h).core then (0:Cell b) else 1) M m:=by
  intro p
  let r:=row H G M p
  let a:=«meta»*7
  let n:=H*chunks G M
  have index: (actorBank hdr a n).read m (r.val:Word w)=(p.1.val:Word w):=
    (bank_read (actorBank hdr a n) m (r.isLt.trans_le (span_ge n)) safe.1.2.2.1).trans (stored.actor p)
  have scalarRead:(rawBank scalar H 0).read m (p.1.val:Word w)=((raw «meta» (records p.1)).val:Word w):=by
    exact (bank_read (rawBank scalar H 0) m (p.1.isLt.trans_le (span_ge H)) safe.1.2.1).trans
      (by simpa [rawBank] using field p.1)
  have maskRead:(maskBank hdr a n).read m (r.val:Word w)=(maskWord a M G p.2.val:Word w):=
    (bank_read (maskBank hdr a n) m (r.isLt.trans_le (span_ge n)) safe.2.1).trans (stored.mask p)
  have one : a≤w:=(Nat.le_mul_of_pos_right a pM).trans wide
  have amt:= (raw «meta» (records p.1)).isLt.trans_le (Nat.pow_le_pow_right (by decide:0<2) one)
  have posA:0<a:=by dsimp [a];omega
  have thresh : (2 : ℕ)^(«meta»*5) < 2^w :=
    Nat.pow_lt_pow_right (by decide:1<2) (show «meta»*5<w by dsimp [a] at one;omega)
  have chosen:DescriptorExpr.Comparison.lt.test ((raw «meta» (records p.1)).val:Word w) (2^(«meta»*5):ℕ)=true ↔ (records p.1).core=false:=by
    simpa only [DescriptorExpr.Comparison.test,decide_eq_true_eq,Fin.lt_def,
      Fin.val_cast_of_lt amt,Fin.val_cast_of_lt thresh] using
      (core_order pMeta (records p.1) (units p.1))
  have u_le:used G M p.2.val≤M:=min_le_left ..
  have top : 2^(a*M)-1<2^w:=by
    have le : 2^(a*M) ≤ 2^w := Nat.pow_le_pow_right (by decide:0<2) wide
    exact (Nat.sub_lt (Nat.two_pow_pos _) (by decide : 0<1)).trans_le le
  have bottom : maskWord a M G p.2.val<2^w:=by
    unfold maskWord
    exact (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide:0<2) (Nat.mul_le_mul_left a u_le)) 1).trans_lt top
  have maskTest : DescriptorExpr.Comparison.eq.test (maskWord a M G p.2.val:Word w)
      ((2^(a*M)-1:ℕ):Word w)=true ↔ used G M p.2.val=M:=by
    change ((maskWord a M G p.2.val:Word w)==((2^(a*M)-1:ℕ):Word w))=true ↔ _
    rw [beq_iff_eq,Fin.ext_iff,Fin.val_cast_of_lt bottom,Fin.val_cast_of_lt top]
    by_cases e:used G M p.2.val=M
    · simp [maskWord,e]
    have cut:=Nat.pow_lt_pow_right (by decide:1<2) (Nat.mul_lt_mul_of_pos_left (lt_of_le_of_ne u_le e) posA)
    have positive:=Nat.two_pow_pos (a*(used G M p.2.val))
    unfold maskWord
    omega
  change (if DescriptorExpr.Comparison.lt.test
      ((rawBank scalar H 0).read m ((actorBank hdr a n).read m (r.val:Word w)))
      ((2^(«meta»*5):ℕ):Word w) then
    (if DescriptorExpr.Comparison.eq.test ((maskBank hdr a n).read m (r.val:Word w))
      ((2^(a*M)-1:ℕ):Word w) then ((flagWord b M M).val:Word w) else
      ((flagWord b M (G%M)).val:Word w)) else ((0:ℕ):Word w)) = _
  rw [index,scalarRead,maskRead]
  by_cases core:(records p.1).core=false
  · rw [ite_eq_left (chosen.mpr core)]
    have want : data (fun h (_:Fin G)=>if (records h).core then (0:Cell b) else 1) p=flagWord b M (used G M p.2.val):=by
      rw [←data_ones (b:=b) p]
      apply congrArg (encode b M)
      funext i
      by_cases live : p.2.val*M+i.val<G <;> simp [live,core]
    rw [want]
    by_cases entire:used G M p.2.val=M
    · rw [ite_eq_left (maskTest.mpr entire),entire]
    · rw [ite_eq_right (fun h=>entire (maskTest.mp h)),chunk_tail pM p.2 (lt_of_le_of_ne u_le entire)]
  · rw [ite_eq_right (fun h=>core (chosen.mp h))]
    have yes:(records p.1).core=true:=by cases eqn:(records p.1).core <;> simp_all
    have zero:data (fun h (_:Fin G)=>if (records h).core then (0:Cell b) else 1) p=0:=by
      have eq_:data (fun h (_:Fin G)=>if (records h).core then (0:Cell b) else 1) p=encode b M (fun _=>0):=by
        apply congrArg (encode b M)
        funext j
        by_cases live : p.2.val*M+j.val<G <;> simp [live,yes]
      rw [eq_]
      apply Fin.ext
      simp [encode]
    rw [zero]
    rfl

end
end Hierarchy.DescentRetainedHubFlag

end OAI
