import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Read the completed signed stem at the relay, at the original SIMD chunk -/
namespace Hierarchy.DescentResetTrunkGather
open DescentSIMDLookup DescentPackedZip DescentDyadicSpan DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM DescriptorExpr PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M b w : ℕ}

def address (alt : Fin H→Option (Fin H)) (G M j : ℕ) : ℕ :=
  if jv : j<H*chunks G M then
    let p:=(row H G M).symm ⟨j,jv⟩
    (alt p.1).elim (H*chunks G M) (fun v=>(row H G M (v,p.2)).val)
  else 0

def phase (w base G M : ℕ) (alt : Fin H→Option (Fin H)) : NativePhase w :=
  let n:=H*chunks G M
  ⟨DescentStaticWordColumn.program w base (address alt G M) n,4+10*n,
    fun m=>DescentStaticWordColumn.image base (address alt G M) m n,DescentStaticWordColumn.cheap w base (address alt G M) n⟩

def table (base n : ℕ) : Bank:=⟨base,Nat.clog 2 n⟩
def issue (n base : ℕ) (old : Bank) : Expr:=
  let index:=Expr.lookup (table base n) .row
  .branch .eq index (.lit n) (.lit 0) (.lookup old index)

theorem work (n base : ℕ) (old : Bank) : (issue n base old).work=22:=rfl

/-- The numerical source and destination row tables may be produced by a
previous native computation, including a measured dense-to-raw-to-dense lookup. -/
theorem from_words (alt : Fin H→Option (Fin H)) (base out : ℕ) (m : Memory w)
    (old : Bank) (v : Fin H→Fin G→Cell b)
    (before : old.Fits w out) (cap : H*chunks G M≤old.size)
    (f : (table base (H*chunks G M)).Fits w out)
    (cells : ∀p : Row H G M,m (old.base+(row H G M p).val)=((data v p).val:Word w))
    (ptr : ∀p : Row H G M,m (base+(row H G M p).val)=
      ((alt p.1).elim (H*chunks G M) (fun t=>(row H G M (t,p.2)).val):Word w)) :
    (issue (H*chunks G M) base old).Fits w out ∧
      Source (issue (H*chunks G M) base old) (fun h g=>(alt h).elim 0 (fun t=>v t g)) M m := by
  let n:=H*chunks G M
  have size : n≤(table base n).size:=span_ge _
  have nword : n<2^w:=size.trans_lt f.2.1
  refine ⟨⟨⟨f,trivial⟩,trivial,trivial,before,f,trivial⟩,?_⟩
  intro p
  let index := (table base n).read m ((row H G M p).val:Word w)
  have actual : index = (alt p.1).elim ((H : Word w) * (chunks G M : Word w))
      (fun t => ((row H G M (t,p.2)).val : Word w)) :=
    (bank_read (table base n) m ((row H G M p).isLt.trans_le size) f).trans (ptr p)
  change (if (index == (n : Word w)) = true then (0 : Word w) else old.read m index) = _
  cases eqn : alt p.1 with
  | none=>
    have sentinel : index = (n : Word w) := by
      simpa only [eqn,Option.elim_none,n,Nat.cast_mul] using actual
    have empty : (data (fun h g=>(alt h).elim 0 (fun t=>v t g)) p).val=0:=by
      change (finFunctionFinEquiv (fun j : Fin M=>if hj : p.2.val*M+j.val<G then
        (alt p.1).elim (0:Cell b) (fun t=>v t ⟨_,hj⟩) else 0)).val=0
      simp [eqn]
    simp only [sentinel,beq_self_eq_true,ite_true,empty,Nat.cast_zero]
  | some t=>
    let ix:=row H G M (t,p.2)
    have pointer : index = (ix.val : Word w) := by
      simpa only [eqn,Option.elim_some] using actual
    have neq : ((ix.val:Word w)==(n:Word w))=false:=by
      apply beq_eq_false_iff_ne.mpr
      intro bad
      have hh:=congrArg Fin.val bad
      rw [Fin.val_cast_of_lt (ix.isLt.trans nword),Fin.val_cast_of_lt nword] at hh
      exact (Nat.ne_of_lt ix.isLt) hh
    have image : data (fun h g=>(alt h).elim 0 (fun t=>v t g)) p=data v (t,p.2):=by
      simp only [data,eqn,Option.elim_some]
    rw [image,pointer,neq,ite_eq_right (by decide : ¬false=true),
      bank_read old m (ix.isLt.trans_le cap) before]
    exact cells (t,p.2)

/-- The only new words are publicly determined row ordinals. The complete
original stem bank supplies all signed, marked, or vacant records. -/
theorem run_at (alt : Fin H→Option (Fin H)) (base : ℕ) (m : Memory w)
    (room : base+span (H*chunks G M)<2^w) :
    let n:=H*chunks G M
    let a:=phase w base G M alt
    a.Runs m ∧ (∀x,x<base ∨ base+n≤x→a.image m x=m x) ∧
      ∀(old : Bank) (v : Fin H→Fin G→Cell b),old.Fits w (base+span n) → old.base+n≤base→n≤old.size→
      (∀p : Row H G M,m (old.base+(row H G M p).val)=((data v p).val:Word w))→
      (issue n base old).Fits w (base+span n) ∧ Source (issue n base old)
        (fun h g=>(alt h).elim 0 (fun t=>v t g)) M (a.image m) :=by
  intro n a
  have size : n≤ span n:=span_ge _
  have nword : n<2^w:=size.trans_lt ((Nat.le_add_left ..).trans_lt room)
  have f : (table base n).Fits w (base+span n):=⟨span_pos _,(Nat.le_add_left ..).trans_lt room,le_rfl⟩
  have stay (x : ℕ) (hx : x<base ∨ base+n≤x) : a.image m x=m x:=
    DescentStaticWordColumn.frame _ _ _ _ x hx
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ ((Nat.add_le_add_left size base).trans_lt room),stay,?_⟩
  intro old v before used cap cells
  apply from_words alt base (base+span n) (a.image m) old v before cap f
  · intro p
    have inside : old.base+(row H G M p).val<base:=(Nat.add_lt_add_left (row H G M p).isLt _).trans_le used
    exact (stay _ (.inl inside)).trans (cells p)
  · intro p
    change DescentStaticWordColumn.image base (address alt G M) m n (base+(row H G M p).val)=_
    rw [DescentStaticWordColumn.read _ _ _ _ (row H G M p).isLt]
    have back : (row H G M).symm ⟨(row H G M p).val,(row H G M p).isLt⟩ = p :=
      (row H G M).symm_apply_apply p
    simp only [address,dite_eq_left (row H G M p).isLt,back]
    cases alt p.1 <;> simp [Nat.cast_mul]

theorem run (alt : Fin H→Option (Fin H)) (base : ℕ) (m : Memory w)
    (room : base+span (H*chunks G M)<2^w) :
    let n:=H*chunks G M
    let a:=phase w base G M alt
    a.Runs m ∧ (∀x,x<base ∨ base+n≤x→a.image m x=m x) ∧
      ∀(old : Bank) (v : Fin H→Fin G→Cell b),old.Fits w base→n≤old.size→
      (∀p : Row H G M,m (old.base+(row H G M p).val)=((data v p).val:Word w))→
      (issue n base old).Fits w (base+span n) ∧ Source (issue n base old)
        (fun h g=>(alt h).elim 0 (fun t=>v t g)) M (a.image m) :=by
  intro n a
  have all:=run_at (M:=M) (G:=G) (b:=b) alt base m room
  refine ⟨all.1,all.2.1,?_⟩
  intro old v before cap cells
  have fit : old.Fits w (base+span n):=⟨before.1,before.2.1,before.2.2.trans (Nat.le_add_right ..)⟩
  exact all.2.2 old v fit ((Nat.add_le_add_left cap _).trans before.2.2) cap cells

end
end Hierarchy.DescentResetTrunkGather

end OAI
