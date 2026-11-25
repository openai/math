import OAI.Hierarchy.DescentResetPackedOrder
import OAI.Hierarchy.DescentResetPackedSplit
import OAI.Hierarchy.DescentPackedCensusRAM
import OAI.Hierarchy.DescentResetCutoffTable

namespace OAI
/-! # Actual packed read expressions for weights, split votes and the shared host parameters -/
namespace Hierarchy.DescentPlainTerminal.Suffix.Readers
open DescentColonies DescentColonies.PackedSplit DescentPackedColony DescentSIMDLookup DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {r b n H G M w : ℕ}

def amount (j : Block r) (z : Cell (b*2^r)) : Cell n := ((encode b (2^r)).symm z j).val

theorem zeroDigits (b s : ℕ) : (encode b s).symm 0=(fun _=>0) := by
  apply (encode b s).symm_apply_eq.mpr
  symm
  apply Fin.ext
  simp [encode]

theorem amount_zero (j : Block r) : amount (n:=n) (b:=b) j 0=0 := by simp [amount,zeroDigits]

theorem amount_source (j : Block r) (rom : Bank) (source : Expr) (out : ℕ)
    (m : Memory w) (wt : Fin H→Fin G→Block r→ℕ) (small : ∀v g i,wt v g i<2^b)
    (fit : rom.Fits w out) (shape : rom.bits=(b*2^r)*M)
    (static : ∀i:Cell ((b*2^r)*M),m (rom.base+i.val)=((DescentSIMDLookup.table (amount (n:=n) (b:=b) j) i).val:Word w))
    (packed : Source source (fun v g=>counts b (wt v g)) M m) :
    Source (PackedOrder.projected rom source) (fun v g=>(wt v g j:Cell n)) M m := by
  have real:=PackedOrder.project rom source out (amount (n:=n) (b:=b) j) (amount_zero j) m
    (fun v g=>counts b (wt v g)) fit shape static packed
  simpa only [amount,counts,Equiv.symm_apply_apply,Fin.val_cast_of_lt (small _ _ _)] using real

def vote (d : Fin r) (j : Block r) (z : Panel r) : Cell n :=
  if z=0 then 0 else ((decodeFlags (strip z) d j).toNat:ℕ)

theorem vote_source (d : Fin r) (j : Block r) (rom : Bank) (source : Expr) (out : ℕ)
    (m : Memory w) (rows : Fin G→Scan.Buffer (Fin H) r)
    (fit : rom.Fits w out) (shape : rom.bits=(1+r*2^r)*M)
    (static : ∀i:Cell ((1+r*2^r)*M),m (rom.base+i.val)=((DescentSIMDLookup.table (vote (n:=n) d j) i).val:Word w))
    (packed : Source source (fun v g=>cache (rows g) v) M m) :
    Source (PackedOrder.projected rom source)
      (fun v g=>((Scan.lookup (rows g) d.val v j).toNat:Cell n)) M m := by
  have real:=PackedOrder.project rom source out (vote (n:=n) d j) (by simp [vote]) m
    (fun v g=>cache (rows g) v) fit shape static packed
  simpa only [cache,flags,vote,ite_eq_right (present_ne_zero _),strip_present,decode_encodeFlags,actualFlags] using real

/-- A short host scalar is repeated at each lane, clearing the final padding mask.
The selected scalar itself can come from a real measured row or a threshold lookup. -/
def broadcast (dict mask : Bank) (e : Expr) : Expr := .op .mask (.lookup dict e) (.lookup mask .row)

def BroadcastROM (dict mask : Bank) (H G M n : ℕ) (m : Memory w) : Prop :=
  (∀i:Cell n,m (dict.base+i.val)=((encode n M (fun _=>i)).val:Word w)) ∧
  ∀p : Row H G M,m (mask.base+(DescentSIMDLookup.row H G M p).val)=(maskWord n M G p.2.val:Word w)

theorem broadcast_source (dict mask : Bank) (src : Expr) (v : Fin H→Cell n) (m : Memory w) (out : ℕ)
    (fitD : dict.Fits w out) (fitM : mask.Fits w out) (size : dict.bits=n)
    (nrow : H*chunks G M≤ mask.size) (width : n*M≤w)
    (publicWords : BroadcastROM dict mask H G M n m)
    (word : ∀p : Row H G M,src.eval m ((DescentSIMDLookup.row H G M p).val:Word w)=(v p.1).val) :
    Source (broadcast dict mask src) (fun h (_ : Fin G) => v h) M m := by
  intro p
  have hd : (v p.1).val < dict.size := by simp [Bank.size,size]
  have hm : (DescentSIMDLookup.row H G M p).val < mask.size :=
    (DescentSIMDLookup.row H G M p).isLt.trans_le nrow
  have cells : (encode n M (fun _ => v p.1)).val < 2^w :=
    (encode n M (fun _ => v p.1)).isLt.trans_le (Nat.pow_le_pow_right (by decide) width)
  have power : n * used G M p.2.val ≤ w :=
    (Nat.mul_le_mul_left n (Nat.min_le_left ..)).trans width
  have masks : maskWord n M G p.2.val < 2^w :=
    (Nat.pred_lt (Nat.two_pow_pos (n * used G M p.2.val)).ne').trans_le
      (Nat.pow_le_pow_right (by decide) power)
  have chunk : (encode n M (fun _ => v p.1)).val % 2^(n * used G M p.2.val) =
      (data (fun h (_ : Fin G) => v h) p).val := by
    have active := DescentSixParty.PackedCensus.masked_data (fun _ : Cell 0 => v p.1)
      (fun (_ : Fin H) (_ : Fin G) => 0) p
    simpa only [masked,DescentSIMDLookup.table,data,Function.comp_def] using active
  change BinaryOp.bitAnd.eval
    (dict.read m (src.eval m ((DescentSIMDLookup.row H G M p).val : Word w)))
    (mask.read m ((DescentSIMDLookup.row H G M p).val : Word w)) = _
  rw [word p,DescentPackedZip.bank_read dict m hd fitD,publicWords.1 (v p.1),
    DescentPackedZip.bank_read mask m hm fitM,publicWords.2 p,←chunk]
  change (((((encode n M (fun _ => v p.1)).val : Word w).val &&&
    ((maskWord n M G p.2.val : Word w).val)) : ℕ) : Word w) = _
  rw [Fin.val_cast_of_lt cells,Fin.val_cast_of_lt masks]
  exact congrArg (fun z : ℕ => (z : Word w)) (Nat.and_two_pow_sub_one_eq_mod _ _)

end
end Hierarchy.DescentPlainTerminal.Suffix.Readers

end OAI
