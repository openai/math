import OAI.Hierarchy.DescentResetPeerUnionRAM
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Shared lookup tables reduce short raw-parent fields across all packed groups -/
namespace Hierarchy.DescentResetPeerUnionRAM.Packed
open DescentSIMDLookup ProtocolRAM DescentIssuedTerminalId
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D E H G b M w : ℕ}

def query (test : Cell b→Bool) (key : Cell (b*M)) : Bool :=
  decide (∃j : Fin M,test ((encode b M).symm key j)=true)

def slot (d : Fin D) (e : Fin E) : Fin (D*E) := finProdFinEquiv (d,e)
def dictionary (base b M : ℕ) (d : Fin D) (e : Fin E) : Bank :=
  ⟨base+(slot d e).val*2^(b*M),b*M⟩
def words (D E b M : ℕ) := D*E*2^(b*M)

def literal (test : Fin D→Fin E→Cell b→Bool) (M : ℕ) (i : ℕ) : ℕ :=
  if h : i < words D E b M then
    let p:=finProdFinEquiv.symm (⟨i,h⟩ : Fin ((D*E)*2^(b*M)))
    let ds:=finProdFinEquiv.symm p.1
    (query (test ds.1 ds.2) p.2).toNat
  else 0

theorem literal_at (test : Fin D→Fin E→Cell b→Bool) (M : ℕ) (d : Fin D) (e : Fin E)
    (x : Cell (b*M)) :
    literal test M ((slot d e).val*2^(b*M)+x.val)=(query (test d e) x).toNat := by
  let i : Fin ((D*E)*2^(b*M)):=finProdFinEquiv (slot d e,x)
  have eqn : i.val=(slot d e).val*2^(b*M)+x.val := by
    simp only [i,finProdFinEquiv_apply_val,Nat.mul_comm (2^(b*M)),Nat.add_comm]
  have inside : i.val < words D E b M := i.isLt
  rw [←eqn,literal,dite_eq_left inside]
  change (query (test (finProdFinEquiv.symm (finProdFinEquiv.symm i).1).1
    (finProdFinEquiv.symm (finProdFinEquiv.symm i).1).2) (finProdFinEquiv.symm i).2).toNat = _
  simp only [i,slot,Equiv.symm_apply_apply]

def inputs (base : ℕ) (other : Fin D→Expr) (src : Fin E→Fin (chunks G M)→Expr) : Inputs D (E*chunks G M) where
  other:=other
  evidence d i:=let p:=finProdFinEquiv.symm i
                .lookup (dictionary base b M d p.1) (src p.1 p.2)

/-- Issue the complete static tables once across all hosts and groups. -/
theorem install (base : ℕ) (test : Fin D→Fin E→Cell b→Bool) (M : ℕ) (m : Memory w)
    (room : base+words D E b M < 2^w) :
    let n:=words D E b M
    let after:=DescentStaticWordColumn.image base (literal test M) m n
    let code:=DescentStaticWordColumn.program w base (literal test M) n
    code.Exec m after (4+10*n) ∧ CheapCode code ∧
    (∀ (d : Fin D) (e : Fin E) (x : Cell (b*M)),
      after ((dictionary base b M d e).base+x.val)=((query (M:=M) (test d e) x).toNat:Word w)) ∧
    (∀a,a < base ∨ base+n ≤ a → after a=m a) := by
  dsimp only
  refine ⟨?_,@DescentStaticWordColumn.cheap w base (literal test M) (words D E b M),?_,
    DescentStaticWordColumn.frame base (words D E b M) (literal test M) m⟩
  · intro P R K machine
    exact DescentStaticWordColumn.mount base (words D E b M) (literal test M) m room machine
  intro d e x
  have room' : (slot d e).val*2^(b*M)+x.val < words D E b M := by
    let i : Fin ((D*E)*2^(b*M)) := finProdFinEquiv (slot d e,x)
    have eqn : i.val = (slot d e).val*2^(b*M)+x.val := by
      simp only [i,finProdFinEquiv_apply_val,Nat.mul_comm (2^(b*M)),Nat.add_comm]
    rw [←eqn]
    exact i.isLt
  change DescentStaticWordColumn.image base (literal test M) m (words D E b M)
    (base+(slot d e).val*2^(b*M)+x.val)=_
  rw [Nat.add_assoc,DescentStaticWordColumn.read _ _ _ _ room',literal_at]

theorem query_chunks (test : Cell b→Bool) (values : Fin H→Fin G→Cell b) (pos : 0 < M)
    (padding : test 0=false) (h : Fin H) :
    (∃c : Fin (chunks G M),query test (data (M:=M) values (h,c))=true) ↔ ∃g,test (values h g)=true := by
  constructor
  · rintro ⟨c,yes⟩
    obtain ⟨j,hit⟩:=of_decide_eq_true yes
    simp only [data,Equiv.symm_apply_apply] at hit
    split at hit
    · exact ⟨_,hit⟩
    · simp [padding] at hit
  · rintro ⟨g,yes⟩
    let p:=position h g pos
    let j:=lane g pos
    have coord : p.2.val*M+j.val=g.val:=Nat.div_add_mod' ..
    refine ⟨p.2,decide_eq_true ?_⟩
    refine ⟨j,?_⟩
    simp only [data,Equiv.symm_apply_apply,dite_eq_left (coord.trans_lt g.isLt)]
    exact (congrArg (fun t : Fin G=>test (values h t)) (Fin.ext coord)).trans yes

/-- The OR in the actual peer program tests the presence of any true original
lane, including records with a zero width. Cells outside the original group
range contribute the zero record and are rejected by the same static test. -/
theorem hit (base : ℕ) (test : Fin D→Fin E→Cell b→Bool) (other : Fin D→Expr)
    (src : Fin E→Fin (chunks G M)→Expr) (values : Fin E→Fin H→Fin G→Cell b)
    (m : Memory w) (pos : 0 < M) (padding : ∀d e,test d e 0=false)
    (fit : 2^(b*M) < 2^w) (high : 1 < 2^w)
    (stored : ∀ (d : Fin D) (e : Fin E) (x : Cell (b*M)),
      m ((dictionary base b M d e).base+x.val)=((query (M:=M) (test d e) x).toNat:Word w))
    (rows : ∀e h c,(src e c).eval m (h.val:Word w)=((data (M:=M) (values e) (h,c)).val:Word w))
    (h : Fin H) (j : Fin D) :
    (∃l,((inputs (b:=b) (G:=G) (M:=M) base other src).evidence j l).eval m (h.val:Word w) ≠ 0) ↔
      ∃e g,test j e (values e h g)=true := by
  have one : (1:Word w) ≠ 0 := by
    intro bad
    have same:=congrArg Fin.val bad
    change 1 % (2^w) = 0 at same
    rw [Nat.mod_eq_of_lt high] at same
    omega
  have read (e : Fin E) (c : Fin (chunks G M)) :
      ((inputs (b:=b) (G:=G) (M:=M) base other src).evidence j (finProdFinEquiv (e,c))).eval m (h.val:Word w) ≠ 0 ↔
        query (test j e) (data (M:=M) (values e) (h,c))=true := by
    simp only [inputs,Equiv.symm_apply_apply]
    let x:=data (M:=M) (values e) (h,c)
    have lookup:=lookup_nat (dictionary base b M j e) m (h.val:Word w) (src e c) x.val (rows e h c) x.isLt fit
    change (Expr.lookup (dictionary base b M j e) (src e c)).eval m (h.val:Word w) ≠ 0 ↔
      query (M:=M) (test j e) x = true
    rw [lookup,stored j e x]
    cases query (M:=M) (test j e) x <;> simp [one]
  constructor
  · rintro ⟨l,yes⟩
    obtain ⟨⟨e,c⟩,rfl⟩:=finProdFinEquiv.surjective l
    exact ⟨e,(query_chunks _ _ pos (padding j e) h).mp ⟨c,(read e c).mp yes⟩⟩
  · rintro ⟨e,g,yes⟩
    obtain ⟨c,on⟩:=(query_chunks _ _ pos (padding j e) h).mpr ⟨g,yes⟩
    exact ⟨_,(read e c).mpr on⟩

end
end Hierarchy.DescentResetPeerUnionRAM.Packed

end OAI
