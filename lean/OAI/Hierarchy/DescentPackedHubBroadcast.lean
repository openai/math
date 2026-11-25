import OAI.Hierarchy.DescentPackedCensusFromSigned
import OAI.Hierarchy.DescentStaticWordColumn
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Broadcast an actual scalar host flag across only the active group lanes -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census.Broadcast
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section

/-- The two public columns contain the host index and the actual all-live mask
at a packed row. They are independent of the observed host flags. -/
def literal (H G M : ℕ) (a : ℕ) : ℕ :=
  let n:=H*chunks G M
  if first : a<n then ((row H G M).symm ⟨a,first⟩).1.val
  else if second : a-n<n then (data (fun _ : Fin H=>fun _ : Fin G=>(1:Cell 1)) ((row H G M).symm ⟨a-n,second⟩)).val
  else 0

def widthBits (H G M : ℕ) := Nat.clog 2 (H*chunks G M+1)
def result (bank : Bank) (origin H G M : ℕ) :=
  let bits:=widthBits H G M
  let ids : Bank:=⟨origin,bits⟩
  let flags : Bank:=⟨origin+H*chunks G M,bits⟩
  Expr.branch .eq (.lookup bank (.lookup ids .row)) (.lit 0) (.lit 0) (.lookup flags .row)

theorem work (bank : Bank) (origin H G M : ℕ) : (result bank origin H G M).work=22 := by rfl

theorem flag_source {w : ℕ} (bank : Bank) (origin H G M : ℕ) (flag : Fin H→Cell 1) (m : Memory w)
    (actual : ∀h,m (bank.base+h.val)=(flag h).val)
    (fit : bank.Fits w origin) (range : H≤bank.size) (room : origin+H*chunks G M+2^(widthBits H G M)<2^w) :
    let n:=H*chunks G M
    let out:=DescentStaticWordColumn.image origin (literal H G M) m (2*n)
    let endAt:=origin+n+2^(widthBits H G M)
    (DescentStaticWordColumn.program w origin (literal H G M) (2*n)).Exec m out (4+10*(2*n)) ∧
      Source (result bank origin H G M) (fun h (_ : Fin G)=>flag h) M out ∧
      (result bank origin H G M).Fits w endAt ∧
      (∀j,j<origin ∨ origin+2*n≤j → out j=m j) := by
  let n:=H*chunks G M
  let u:=2^(widthBits H G M)
  let out:=DescentStaticWordColumn.image origin (literal H G M) m (2*n)
  let endAt:=origin+n+u
  let A : Bank:=⟨origin,widthBits H G M⟩
  let B : Bank:=⟨origin+n,widthBits H G M⟩
  have shape : n≤u := (Nat.le_succ n).trans (Nat.le_pow_clog (by decide) _)
  have last : origin+2*n≤endAt := by dsimp only [endAt];omega
  have endFits : origin+n+u<2^w := room
  have af : A.Fits w endAt := by
    refine ⟨Nat.two_pow_pos _,?_,?_⟩
    · change u<2^w
      omega
    · change origin+u≤origin+n+u
      omega
  have bf : B.Fits w endAt := ⟨Nat.two_pow_pos _,af.2.1,le_rfl⟩
  have old : bank.Fits w endAt:=⟨fit.1,fit.2.1,fit.2.2.trans (by dsimp [endAt];omega)⟩
  have keep (j : ℕ) (hj : j<origin ∨ origin+2*n≤j) : out j=m j :=
    DescentStaticWordColumn.frame origin (2*n) (literal H G M) m j hj
  refine ⟨DescentStaticWordColumn.mount _ _ _ m (last.trans_lt room),?_,⟨⟨old,af,trivial⟩,trivial,trivial,bf,trivial⟩,keep⟩
  intro p
  let i:=row H G M p
  have low (j : ℕ) (hj : j<2*n) : out (origin+j)=(literal H G M j:Word w) :=
    DescentStaticWordColumn.read origin (2*n) (literal H G M) m (j:=j) hj
  have aid : out (A.base+i.val)=(p.1.val:Word w) := by
    rw [show A.base=origin from rfl,low _ (by have:=i.isLt;omega)]
    simp [literal,i]
  have mask : out (B.base+i.val)=((data (fun _ : Fin H=>fun _ : Fin G=>(1:Cell 1)) p).val:Word w) := by
    rw [show B.base=origin+n from rfl,Nat.add_assoc,low _ (by have:=i.isLt;omega)]
    simp [literal,show ¬n+i.val<n by omega,i,n]
  have rd := (keep (bank.base+p.1.val) (.inl ((Nat.add_lt_add_left (p.1.isLt.trans_le range) _).trans_le fit.2.2))).trans (actual p.1)
  have readFlag : bank.read out (A.read out (i.val:Word w))=((flag p.1).val:Word w) := by
    rw [bank_read A out (i.isLt.trans_le shape) af,aid,
      bank_read bank out (p.1.isLt.trans_le range) old,rd]
  have readMask := (bank_read B out (i.isLt.trans_le shape) bf).trans mask
  change (if Comparison.eq.test (bank.read out (A.read out (i.val:Word w))) 0 then
    0 else B.read out (i.val:Word w)) = _
  simp only [readFlag,readMask]
  have flagFits : 1<2^w := by
    have positive : 0<origin+n+u := by dsimp only [u];positivity
    omega
  have oneWord : (1:Word w)≠0 := by
    intro impossible
    apply Nat.one_ne_zero
    simpa only [show (1:Word w)=((1:ℕ):Word w) from rfl,Fin.val_cast_of_lt flagFits,Fin.val_zero]
      using congrArg Fin.val impossible
  by_cases h : flag p.1=0
  · simp [h,Comparison.test,data,encode]
  · have binary : ∀ x : Fin 2, x ≠ 0 → x = 1 := by decide
    have one : flag p.1=1 := binary (flag p.1) h
    simp [one,Comparison.test,oneWord,data]


end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census.Broadcast

end OAI
