import OAI.Hierarchy.GridPinPublisherLayout
import OAI.Hierarchy.GridPinNativeLoops
import OAI.Hierarchy.FactorBucketInputs
import OAI.Hierarchy.GridPassageRAMState

namespace OAI
/-! # Exact addresses and values of the native prefix and source-pin writes -/

namespace Hierarchy.GridPinNativeLoops
open Computability.VPVNP.BurstRAM PrivateRAM
open FactorBucketRAM
open scoped Fin.CommRing

variable {w : ℕ}
private theorem div_word {a b : ℕ} (ha : a<2^w) (hb : b<2^w) :
    BinaryOp.div.eval (a:Word w) (b:Word w) = ((a/b:ℕ):Word w) := by
  simp [BinaryOp.eval,Fin.val_cast_of_lt ha,Fin.val_cast_of_lt hb]

private theorem mod_word {a b : ℕ} (ha : a<2^w) (hb : b<2^w) :
    BinaryOp.mod.eval (a:Word w) (b:Word w) = ((a%b:ℕ):Word w) := by
  simp [BinaryOp.eval,Fin.val_cast_of_lt ha,Fin.val_cast_of_lt hb]

private theorem nonzero (z : Word w) : BinaryOp.div.eval z z = if z=0 then 0 else 1 := by
  by_cases h : z=0
  · subst z; simp [BinaryOp.eval]
  · have hp : 0<z.val := Nat.pos_of_ne_zero (fun zero => h (Fin.ext (by simpa using zero)))
    simp [BinaryOp.eval,Nat.div_self hp,h]

def seedWords (w count dst stride initial : ℕ) : Parameters w :=
  ![count,dst,stride,initial,0,0,0,0,0,0,0,0]

theorem seedStep_natural (count dst stride initial i : ℕ) (m : Memory w) (fit : dst+i<2^w) :
    seedStep (seedWords w count dst stride initial) (i:Word w) m =
    Function.update m (dst+i) ((i*stride+initial:ℕ):Word w) := by
  change writeMemory m ((dst:Word w)+(i:Word w))
    ((i:Word w)*(stride:Word w)+(initial:Word w))=_
  simp only [← Nat.cast_add,← Nat.cast_mul,GridPassageRAMRow.writeMemory_nat _ _ fit]

def factorWords (w count : ℕ) (p : FactorBanks) : Parameters w :=
  ![count,p.items,p.keys,p.owners,p.resource,p.stride,p.ticks,p.bases,p.amount,0,0,0]

/-- The mask inside the machine's factor loop permits precisely the encoded
geometric bucket chosen by this iteration. -/
theorem factorStep_natural (p : FactorBanks) (count i : ℕ) (m : Memory w)
    (fi : i<2^w) (fn : p.items<2^w)
    (f cl : ℕ) (row : i%p.items=f) (key : i/p.items=cl)
    (keyAddr : p.keys+f<2^w) (ownerAddr : p.owners+f<2^w)
    (lenAddr : p.resource+f*p.stride+p.amount<2^w) (baseAddr : p.bases+f<2^w)
    (cursorAddr : p.ticks+(m (p.owners+f)).val<2^w) :
    factorStep (factorWords w count p) (i:Word w) m =
      if (m (p.keys+f)).val=cl then
        let cp := p.ticks+(m (p.owners+f)).val
        Function.update (Function.update m (p.bases+f) (m cp)) cp
          (m cp+m (p.resource+f*p.stride+p.amount)) else m := by
  have fcl : cl<2^w := by rw [←key]; exact (Nat.div_le_self _ _).trans_lt fi
  let cursor := p.ticks+(m (p.owners+f)).val
  have cp : (p.ticks:Word w)+m (p.owners+f)=((cursor:ℕ):Word w) := by
    simp [cursor]
  simp only [factorStep,
    show factorWords w count p 1 = (p.items : Word w) from rfl,
    show factorWords w count p 2 = (p.keys : Word w) from rfl,
    show factorWords w count p 3 = (p.owners : Word w) from rfl,
    show factorWords w count p 4 = (p.resource : Word w) from rfl,
    show factorWords w count p 5 = (p.stride : Word w) from rfl,
    show factorWords w count p 6 = (p.ticks : Word w) from rfl,
    show factorWords w count p 7 = (p.bases : Word w) from rfl,
    show factorWords w count p 8 = (p.amount : Word w) from rfl,
    div_word fi fn,mod_word fi fn,
    key,row,←Nat.cast_mul,←Nat.cast_add,Fin.val_cast_of_lt keyAddr,Fin.val_cast_of_lt ownerAddr,
    Fin.val_cast_of_lt baseAddr,Fin.val_cast_of_lt lenAddr]
  rw [cp,Fin.val_cast_of_lt cursorAddr]
  have cmp : m (p.keys+f)-(cl:Word w)=0 ↔ (m (p.keys+f)).val=cl := by
    rw [sub_eq_zero,Fin.ext_iff,Fin.val_cast_of_lt fcl]
  change (writeMemory (writeMemory m _ (_+(_-_)*(1-BinaryOp.div.eval _ _))) _
    (_+_*(1-BinaryOp.div.eval _ _)))=_
  rw [nonzero,if_congr cmp rfl rfl]
  by_cases matchKey : (m (p.keys+f)).val=cl
  · simp only [matchKey,ite_true,sub_zero,mul_one]
    rw [GridPassageRAMRow.writeMemory_nat _ _ baseAddr,GridPassageRAMRow.writeMemory_nat _ _ cursorAddr]
    congr 2; abel
  · simp only [matchKey,ite_false,sub_self,mul_zero,add_zero]
    rw [GridPassageRAMRow.writeMemory_nat _ _ baseAddr,GridPassageRAMRow.writeMemory_nat _ _ cursorAddr]
    simp only [Function.update_eq_self]

def bucketWords (w count : ℕ) (p : BucketBanks) : Parameters w :=
  ![count,p.span,p.cap,p.owners,p.cursors,p.blocks,0,0,0,0,0,0]

private theorem clipped (rem span : ℕ) (rfit : rem<2^w) (sfit : span<2^w) (pos : 0< span) :
    (rem:Word w)+((span:Word w)-(rem:Word w))*
      BinaryOp.div.eval (BinaryOp.div.eval (rem:Word w) (span:Word w))
        (BinaryOp.div.eval (rem:Word w) (span:Word w)) = ((min span rem:ℕ):Word w) := by
  rw [div_word rfit sfit,nonzero]
  have fit := (Nat.div_le_self rem span).trans_lt rfit
  have zero : ((rem/span:ℕ):Word w)=0 ↔ rem/span=0 := by
    rw [Fin.ext_iff,Fin.val_cast_of_lt fit];rfl
  rw [if_congr zero rfl rfl]
  by_cases smaller : rem< span
  · simp [Nat.div_eq_of_lt smaller,Nat.min_eq_right smaller.le]
  · have le : span≤rem := by omega
    simp [Nat.ne_of_gt (Nat.div_pos le pos),Nat.min_eq_left le]


/-- One nonempty original bucket contributes precisely its clipped length to
the cursor of its own factor. No word belonging to another factor changes. -/
theorem bucketStep_natural (p : BucketBanks) (count i : ℕ) (m : Memory w)
    (_fi : i<2^w) (fs : p.span<2^w) (fc : p.cap<2^w) (pos : 0<p.span)
    (active : i*p.span≤p.cap) (fo : p.owners+i<2^w) (fb : p.blocks+i<2^w)
    (fcursor : p.cursors+(m (p.owners+i)).val<2^w) :
    bucketStep (bucketWords w count p) (i:Word w) m =
      let cp := p.cursors+(m (p.owners+i)).val
      Function.update (Function.update m (p.blocks+i) (m cp)) cp
        (m cp+(FactorPinIntervals.bucketLength p.cap p.span i:Word w)) := by
  let cp := p.cursors+(m (p.owners+i)).val
  have ptr : (p.cursors:Word w)+m (p.owners+i)=(cp:Word w) := by simp [cp]
  have remFit : p.cap-i*p.span<2^w := (Nat.sub_le _ _).trans_lt fc
  simp only [bucketStep,
    show bucketWords w count p 1 = (p.span : Word w) from rfl,
    show bucketWords w count p 2 = (p.cap : Word w) from rfl,
    show bucketWords w count p 3 = (p.owners : Word w) from rfl,
    show bucketWords w count p 4 = (p.cursors : Word w) from rfl,
    show bucketWords w count p 5 = (p.blocks : Word w) from rfl,
    ←Nat.cast_mul,
    ←Nat.cast_add,Fin.val_cast_of_lt fo,←Nat.cast_sub active,ptr]
  change writeMemory (writeMemory m _ _) _ (_+(_+(_-_)*BinaryOp.div.eval _ _))=_
  rw [clipped _ _ remFit fs pos,
    GridPassageRAMRow.writeMemory_nat _ _ fb,GridPassageRAMRow.writeMemory_nat _ _ fcursor]
  rw [Fin.val_cast_of_lt (show cp < 2^w from fcursor)]; rfl

def literalWords (w count : ℕ) (p : SourceBanks) : Parameters w :=
  ![count,p.span,p.external,p.blocks,p.originals,p.literal,0,0,0,0,0,0]

def endpointWords (w count : ℕ) (p : SourceBanks) : Parameters w :=
  ![count,p.span,p.rails,p.blocks,p.dest,0,0,0,0,0,0,0]

theorem stone_natural (m : Memory w) (span blocks j : ℕ)
    (fs : span<2^w) (fj : j<2^w) (fb : blocks+j/span<2^w) :
    stone m (span:Word w) blocks j=m (blocks+j/span)+((j%span:ℕ):Word w) := by
  simp only [stone,div_word fj fs,mod_word fj fs,←Nat.cast_add,Fin.val_cast_of_lt fb]

theorem literalStep_natural (p : SourceBanks) (count i : ℕ) (m : Memory w)
    (fs : p.span<2^w) (j : ℕ) (atBit : p.external+i=j) (fj : j<2^w)
    (fb : p.blocks+j/p.span<2^w) (fo : p.originals+j<2^w)
    (dst : ℕ) (base : m (p.blocks+j/p.span)+((j%p.span:ℕ):Word w)=(dst:Word w))
    (fd : p.literal+dst<2^w) :
    literalStep (literalWords w count p) (i:Word w) m =
      Function.update m (p.literal+dst) (m (p.originals+j)) := by
  change writeMemory m ((p.literal:Word w) + stone m p.span p.blocks ((p.external:Word w)+i))
    (m ((p.originals:Word w)+((p.external:Word w)+i)).val)=_
  simp only [←Nat.cast_add,atBit,stone_natural _ _ _ _ fs fj fb,base,
    Fin.val_cast_of_lt fo,GridPassageRAMRow.writeMemory_nat _ _ fd]

theorem endpointStep_natural (p : SourceBanks) (count i : ℕ) (m : Memory w)
    (two : 2<2^w) (fi : i<2^w) (fs : p.span<2^w) (fr : p.rails+i/2<2^w)
    (orig j : ℕ) (mapped : m (p.rails+i/2)=(orig:Word w)) (split : orig*2+i%2=j)
    (fj : j<2^w) (fb : p.blocks+j/p.span<2^w) (fd : p.dest+i<2^w) :
    endpointStep (endpointWords w count p) (i:Word w) m =
      Function.update m (p.dest+i) (m (p.blocks+j/p.span)+((j%p.span:ℕ):Word w)) := by
  change writeMemory m ((p.dest:Word w)+i)
    (stone m p.span p.blocks
      (m ((p.rails:Word w)+BinaryOp.div.eval (i:Word w) (2:Word w)).val*(2:Word w) +
        BinaryOp.mod.eval (i:Word w) (2:Word w)))=_
  simp only [show (2:Word w)=((2:ℕ):Word w) from rfl,div_word fi two,mod_word fi two,
    ←Nat.cast_add,Fin.val_cast_of_lt fr,mapped,←Nat.cast_mul,split,stone_natural _ _ _ _ fs fj fb,
    GridPassageRAMRow.writeMemory_nat _ _ fd]

end Hierarchy.GridPinNativeLoops

end OAI
