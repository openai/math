import OAI.Hierarchy.DescentPackedRegroup
import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Splitting an existing packed word into smaller dyadic lane groups -/
namespace Hierarchy.DescentSIMDLookup.Subwords
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ThreeFlat.Routing
open scoped Classical Fin.CommRing
noncomputable section
variable {a H G K R M w : ℕ}

theorem chunks_exact (K r : ℕ) (pos : 0<r) : chunks (K*r) r=K := by
  simpa [chunks,poolBatchCount] using chunks_group K 1 r (by decide) pos

def parent (size : G=K*(R*M)) (ratio : 0<R) (pos : 0<M) (p : Row H G M) : Row H G (R*M) :=
  (p.1,⟨p.2.val/R,by
    have new : chunks G M=K*R := by rw [size,←Nat.mul_assoc,chunks_exact _ _ pos]
    have old : chunks G (R*M)=K := by rw [size,chunks_exact _ _ (Nat.mul_pos ratio pos)]
    rw [old,Nat.div_lt_iff_lt_mul ratio]
    exact p.2.isLt.trans_le new.le⟩)

def part (ratio : 0<R) (p : Row H G M) : Fin R:=⟨p.2.val%R,Nat.mod_lt _ ratio⟩

def take (a M : ℕ) (i : Fin R) (z : Cell (a*(R*M))) : Cell (a*M) :=
  encode a M (fun j=>(encode a (R*M)).symm z (finProdFinEquiv (i,j)))

theorem take_at (size : G=K*(R*M)) (ratio : 0<R) (pos : 0<M) (X : Fin H→Fin G→Cell a) (p : Row H G M) :
    take a M (part ratio p) (data X (parent size ratio pos p))=data X p := by
  unfold take data
  apply congrArg (encode a M)
  funext j
  simp only [Equiv.symm_apply_apply]
  have index : (parent size ratio pos p).2.val*(R*M)+(finProdFinEquiv (part ratio p,j)).val=p.2.val*M+j.val := by
    change (p.2.val/R)*(R*M)+(j.val+M*(p.2.val%R))=p.2.val*M+j.val
    have same:=congrArg (·*M) (Nat.div_add_mod p.2.val R)
    nlinarith only [same]
  have eqn : p.2.val/R*(R*M)+(finProdFinEquiv (part ratio p,j)).val=p.2.val*M+j.val:=index
  simp only [parent,eqn]

structure Tables where
  parentRows : Bank
  offsets : Bank
  dictionary : Bank

def term (T : Tables) (input : Bank) : Expr :=
  .lookup T.dictionary (.op .add (.lookup T.offsets .row) (.lookup input (.lookup T.parentRows .row)))

def stride (a R M : ℕ) := 2^(a*(R*M))

def Static (T : Tables) (size : G=K*(R*M)) (ratio : 0<R) (pos : 0<M) (m : Memory w) : Prop :=
  (∀p : Row H G M,m (T.parentRows.base+(row H G M p).val)=((row H G (R*M) (parent size ratio pos p)).val:Word w)) ∧
  (∀p : Row H G M,m (T.offsets.base+(row H G M p).val)=((part ratio p).val*stride a R M:ℕ)) ∧
  ∀(i : Fin R) (z : Cell (a*(R*M))),m (T.dictionary.base+(i.val*stride a R M+z.val))=((take a M i z).val:Word w)

structure Room (T : Tables) (input : Bank) (a H G R M w out : ℕ) : Prop where
  parentFit : T.parentRows.Fits w out
  parentSize : H*chunks G M≤T.parentRows.size
  offsetFit : T.offsets.Fits w out
  offsetSize : H*chunks G M≤T.offsets.size
  dataFit : input.Fits w out
  dataSize : H*chunks G (R*M) ≤ input.size
  dictFit : T.dictionary.Fits w out
  dictSize : R*stride a R M≤T.dictionary.size
  top : out+H*chunks G M<2^w

theorem word_at (T : Tables) (input : Bank) (out : ℕ) (room : Room T input a H G R M w out)
    (size : G=K*(R*M)) (ratio : 0<R) (pos : 0<M) (X : Fin H→Fin G→Cell a) (m : Memory w)
    (rom : Static (a:=a) (H:=H) T size ratio pos m)
    (words : ∀p : Row H G (R*M),m (input.base+(row H G (R*M) p).val)=((data X p).val:Word w))
    (p : Row H G M) : (term T input).eval m ((row H G M p).val:Word w)=((data X p).val:Word w) := by
  let n:=row H G M p
  let old:=parent size ratio pos p
  let j:=part ratio p
  let src:=data X old
  have key : j.val*stride a R M+src.val<T.dictionary.size := by
    have lower:=src.isLt
    change src.val<stride a R M at lower
    have endRow:=Nat.mul_le_mul_right (stride a R M) j.isLt
    rw [Nat.succ_mul] at endRow
    have bound:=room.dictSize
    omega
  have add : ((j.val*stride a R M:ℕ):Word w) + (src.val:Word w)=((j.val*stride a R M+src.val:ℕ):Word w) := by
    rw [Nat.cast_add]
  have parentAddr : T.parentRows.read m (n.val:Word w)=((row H G (R*M) old).val:Word w):=
    (DescentPackedZip.bank_read _ _ (n.isLt.trans_le room.parentSize) room.parentFit).trans (rom.1 p)
  have offset : T.offsets.read m (n.val:Word w)=((j.val*stride a R M:ℕ):Word w):=
    (DescentPackedZip.bank_read _ _ (n.isLt.trans_le room.offsetSize) room.offsetFit).trans (rom.2.1 p)
  have dat : input.read m ((row H G (R*M) old).val:Word w)=(src.val:Word w):=
    (DescentPackedZip.bank_read _ _ ((row H G (R*M) old).isLt.trans_le room.dataSize) room.dataFit).trans (words old)
  change T.dictionary.read m (T.offsets.read m (n.val:Word w)+input.read m (T.parentRows.read m (n.val:Word w)))=_
  rw [offset,parentAddr,dat,add,DescentPackedZip.bank_read T.dictionary m key room.dictFit,rom.2.2 j src]
  exact congrArg (fun t : Cell (a*M)=>(t.val:Word w)) (take_at size ratio pos X p)

theorem run (T : Tables) (input : Bank) (out : ℕ) (room : Room T input a H G R M w out)
    (size : G=K*(R*M)) (ratio : 0<R) (pos : 0<M) (X : Fin H→Fin G→Cell a) (m : Memory w)
    (rom : Static (a:=a) (H:=H) T size ratio pos m)
    (words : ∀p : Row H G (R*M),m (input.base+(row H G (R*M) p).val)=((data X p).val:Word w)) :
    let rows:=H*chunks G M
    let dst:=image out rows (term T input) m
    (scan w out rows (term T input)).Exec m dst (4+rows*(2*(term T input).work+4)) ∧
    CheapCode (scan w out rows (term T input)) ∧ (∀p : Row H G M,dst (out+(row H G M p).val)=((data X p).val:Word w)) ∧
    ∀a,a<out ∨ out+rows≤a→dst a=m a := by
  have fits : (term T input).Fits w out:=⟨room.dictFit,⟨room.offsetFit,trivial⟩,room.dataFit,room.parentFit,trivial⟩
  exact ⟨scan_exec _ _ _ _ fits room.top,(fun pc reg pub exit i=>scan_cheap _ _ _ _ pc reg pub exit i),
    fun p=>(ProtocolRAMGeneratedWrite.read_image ..).trans (word_at T input out room size ratio pos X m rom words p),
    fun a h=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ h⟩


end
end Hierarchy.DescentSIMDLookup.Subwords

end OAI
