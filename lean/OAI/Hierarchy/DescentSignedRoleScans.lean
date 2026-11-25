import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentMaskedLookupBook
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentPackedCensusRAM

namespace OAI
/-! # All role-specific packed transforms of a single previous donor register -/
namespace Hierarchy.DescentSIMDLookup.RoleScans
open DescentPackedColony DescentPackedFlowBatch ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {a b H G M w : ℕ}
def pitch (a H G M : ℕ) := 2^(a*M)+2^(Nat.clog 2 (H*chunks G M))
def home (a H G M pages base : ℕ) := base+pages*pitch a H G M
def banks (a H G M base : ℕ) (src : Bank) (j : ℕ) :=Book.banks (base+j*pitch a H G M) a H G M src
def literal (f : ℕ→Cell a→Cell b) (H G M : ℕ) (i : ℕ) :=
  Book.literal (f (i/pitch a H G M)) H G M (i%pitch a H G M)
def install (f : ℕ→Cell a→Cell b) (H G M w base pages : ℕ) :=
  DescentStaticWordColumn.program w base (literal f H G M) (pages*pitch a H G M)
def table (f : ℕ→Cell a→Cell b) (H G M base pages : ℕ) (m : Memory w) :=
  DescentStaticWordColumn.image base (literal f H G M) m (pages*pitch a H G M)
def jobs (a H G M base pages : ℕ) (src : Bank) :=
  passes (home a H G M pages base) (H*chunks G M) (H*chunks G M) (fun i=>lookup (banks a H G M base src i)) 0 pages
def cpu (f : ℕ→Cell a→Cell b) (H G M w base pages : ℕ) (src : Bank) :=
  (install f H G M w base pages).seq (ProtocolRAM.program w (jobs a H G M base pages src))
def image (f : ℕ→Cell a→Cell b) (H G M base pages : ℕ) (src : Bank) (m : Memory w) :=
  result (jobs a H G M base pages src) (table f H G M base pages m)
def ticks (a H G M pages : ℕ) := (4+10*(pages*pitch a H G M))+(4+pages*(4+44*(H*chunks G M)))
def limit (a H G M base pages : ℕ) := home a H G M pages base+pages*(H*chunks G M)

theorem clock_eq (a H G M base start n out : ℕ) (src : Bank) :
    clock (passes out (H*chunks G M) (H*chunks G M) (fun j=>lookup (banks a H G M base src j)) start n)=
    4+n*(4+44*(H*chunks G M)) :=by
  induction n generalizing start with
  | zero=>simp [passes,clock]
  | succ n ih=>
    simp only [passes,clock,Pass.clock,lookup_work,show 2*20+4=44 by decide,ih]
    ring

theorem arena (base pages : ℕ) (src : Bank) (room : limit a H G M base pages<2^w)
    (source : src.base+src.size≤base) (rows : H*chunks G M ≤ src.size) (width : M*max a b≤w/2)
    (j : Fin pages) : Fits (banks a H G M base src j.val) a b M H G w (home a H G M pages base) :=by
  let n:=H*chunks G M
  let s:=pitch a H G M
  let out:=home a H G M pages base
  have bankEnd : base+j.val*s+s≤out :=by
    dsimp [out,home,s];have le:=Nat.mul_le_mul_right (pitch a H G M) j.isLt
    rw [Nat.succ_mul] at le;omega
  have baseEnd : base≤out:=Nat.le_add_right _ _
  have outFits : out<2^w:=(Nat.le_add_right ..).trans_lt room
  have both : 2^(a*M) ≤ s ∧ 2^(Nat.clog 2 n) ≤ s :=⟨Nat.le_add_right ..,Nat.le_add_left ..⟩
  have word : out+n<2^w:=by
    have count : 1≤pages:=by have:=j.isLt;omega
    have more:=Nat.mul_le_mul_right n count
    dsimp only [limit] at room
    simp only [one_mul] at more
    exact (Nat.add_le_add_left more out).trans_lt room
  refine ⟨⟨by simp [Bank.size],(by omega : src.size≤out).trans_lt outFits,source.trans baseEnd⟩,
    ⟨by simp [banks,Book.banks,Bank.size],?_,?_⟩,⟨by simp [banks,Book.banks,Bank.size],?_,?_⟩,
    rows,rfl,Nat.le_pow_clog (by decide) _,word,width⟩
  · change 2^(a*M)<2^w;omega
  · change base+j.val*s+2^(a*M)≤out;omega
  · change 2^(Nat.clog 2 n)<2^w;omega
  · change base+j.val*s+2^(a*M)+2^(Nat.clog 2 n)≤out
    dsimp only [s,pitch,n] at *;omega

private theorem pin (f : ℕ→Cell a→Cell b) (base pages : ℕ) (src : Bank) (m : Memory w)
    (j : Fin pages) (i : Cell (a*M) ⊕ Fin (H*chunks G M)) :
    table f H G M base pages m (fixedAddr (banks a H G M base src j.val) i)=fixedWord (f j.val) i :=by
  let key:=(finSumFinEquiv i).val
  let s:=pitch a H G M
  have kl:key<Book.words a H G M :=(finSumFinEquiv i).isLt
  have ks:key<s:=kl.trans_le (Nat.add_le_add_left (Nat.le_pow_clog (by decide : 1<2) _) _)
  have index:j.val*s+key<pages*s:=by
    have bound:=Nat.mul_le_mul_right s j.isLt;rw [Nat.succ_mul] at bound;omega
  have pos:0<s:=by omega
  have div:(j.val*s+key)/s=j.val:=by rw [Nat.mul_comm j.val,Nat.mul_add_div pos,Nat.div_eq_of_lt ks,Nat.add_zero]
  have md:(j.val*s+key)%s=key:=by rw [Nat.mul_comm j.val,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt ks]
  rw [show fixedAddr (banks a H G M base src j.val) i=base+(j.val*s+key) from
    (Book.ordinal H G M (base+j.val*s) src i).trans (Nat.add_assoc ..)]
  change DescentStaticWordColumn.image base (literal f H G M) m (pages*s) (base+(j.val*s+key))=_
  rw [DescentStaticWordColumn.read _ _ _ _ index]
  change (Book.literal (f ((j.val*s+key)/s)) H G M ((j.val*s+key)%s):Word w)=_
  rw [div,md]
  have value : Book.literal (f j.val) H G M key=Book.value (f j.val) H G M i:=by
    rw [Book.literal,dite_eq_left kl]
    exact congrArg (Book.value (f j.val) H G M) (finSumFinEquiv.symm_apply_apply i)
  rw [value]
  cases i <;> rfl

theorem any_run (f : ℕ→Cell a→Cell b) (base pages : ℕ) (src : Bank) (m : Memory w)
    (source : src.base+src.size≤base) (rows : H*chunks G M ≤ src.size) (width : M*max a b≤w/2)
    (room : limit a H G M base pages<2^w) :
    (cpu f H G M w base pages src).Exec m (image f H G M base pages src m) (ticks a H G M pages) ∧
    (∀v,v<base ∨ limit a H G M base pages≤v→image f H G M base pages src m v=m v) ∧
    CheapCode (cpu f H G M w base pages src) :=by
  let n:=H*chunks G M
  let out:=home a H G M pages base
  let mid:=table f H G M base pages m
  have before:out<2^w:=(Nat.le_add_right ..).trans_lt room
  have boot : (install f H G M w base pages).Exec m mid (4+10*(pages*pitch a H G M)):=
    DescentStaticWordColumn.mount base (pages*pitch a H G M) (literal f H G M) m before
  have fits (j : ℕ) (less : j<pages) : (lookup (banks a H G M base src j)).Fits w out:=by
    have u:=arena base pages src room source rows width ⟨j,less⟩
    simpa only [lookup,Expr.Fits,and_true] using And.intro (And.intro u.dictionary u.source) u.mask
  obtain ⟨run,_,saved⟩:=DescentPackedFlowBatch.execute out n n pages _ mid fits room le_rfl
  refine ⟨?_,?_,?_⟩
  · unfold cpu image
    rw [show ticks a H G M pages=(4+10*(pages*pitch a H G M))+clock (jobs a H G M base pages src) by
      rw [jobs,clock_eq];rfl]
    exact boot.then run
  · rintro v (pre|post)
    · exact (saved v (pre.trans_le (Nat.le_add_right ..))).trans (DescentStaticWordColumn.frame _ _ _ _ v (.inl pre))
    · exact (DescentPackedFlowBatch.above out n n _ mid 0 pages v le_rfl (by simpa only [limit,out,n,Nat.zero_add] using post)).trans
        (DescentStaticWordColumn.frame _ _ _ _ v (.inr ((Nat.le_add_right ..).trans post)))
  · apply cheap_seq
    · exact DescentStaticWordColumn.cheap _ _ _ _
    · exact ProtocolRAM.program_cheap _ _

theorem read (f : ℕ→Cell a→Cell b) (base pages : ℕ) (src : Bank) (m : Memory w)
    (source : src.base+src.size≤base) (rows : H*chunks G M ≤ src.size) (width : M*max a b≤w/2)
    (room : limit a H G M base pages<2^w) (v : Fin H→Fin G→Cell a) (old : Reads src v M m)
    (j : Fin pages) (p : Row H G M) :
    image f H G M base pages src m (home a H G M pages base+j.val*(H*chunks G M)+(row H G M p).val)=
      ((data (fun h g=>f j.val (v h g)) p).val:Word w) :=by
  let n:=H*chunks G M
  let out:=home a H G M pages base
  let mid:=table f H G M base pages m
  let bank:=banks a H G M base src j.val
  have bound (l : Fin pages):=arena base pages src room source rows width l
  have good (l:ℕ) (lt:l<pages) : (lookup (banks a H G M base src l)).Fits w out:=by
    have h:=bound ⟨l,lt⟩
    simpa only [lookup,Expr.Fits,and_true] using And.intro (And.intro h.dictionary h.source) h.mask
  have live : PinFrame (M:=M) bank (f j.val) v mid:=by
    refine ⟨fun i bit=>congrArg (fun r:Word w=>wordBits w r bit) (pin f base pages src m j i),?_⟩
    intro k;exact (DescentStaticWordColumn.frame _ _ _ _ _ (.inl
      (((Nat.add_lt_add_left (row H G M k).isLt _).trans_le (Nat.add_le_add_left rows _)).trans_le source))).trans (old k)
  have printed:=(DescentPackedFlowBatch.execute out n n pages _ mid good room le_rfl).2.1 j (row H G M p)
  exact printed.trans ((ProtocolRAMGeneratedWrite.read_image out n (lookup bank) mid (row H G M p)).symm.trans
    (DescentSixParty.PackedCensus.col_read bank out (bound j) (f j.val) v mid live p))

end
end Hierarchy.DescentSIMDLookup.RoleScans

end OAI
