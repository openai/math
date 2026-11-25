import OAI.Hierarchy.DescentTerminalPopulationPage
import OAI.Hierarchy.DescentPackedActorRaster

namespace OAI
/-! # Transpose and concatenate the previous actor mask into the terminal occupied channels -/
namespace Hierarchy.DescentTerminalActorRepack
open DescentSIMDLookup DescentTerminalPopulation DescentColonies.SplitRAM DescentTerminalPointerDigits
open DescentOperandStateBanks Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section

variable {w : ℕ} (H G M a B:ℕ) (lo:ℕ)
local notation "J" => chunks G M
local notation "Q" => 2^(a*M)
def head : Bank := ⟨lo,Nat.clog 2 H⟩
def count := (head H lo).size+(B*J)*Q
def tableBank (b:Fin B) (j:Fin J) : Bank :=⟨lo+(head H lo).size+(finProdFinEquiv (b,j)).val*Q,a*M⟩

variable {H G M a B lo} (pick:Fin B→Cell a→Cell 1)

/-- Both original layouts use this format. With block-vector cells, all the
source banks alias the actor page and the projection extracts a block. With
a bank per block, its single-bit payload passes through unchanged. -/
def literal (H G M lo:ℕ) (pick:Fin B→Cell a→Cell 1) (idx:ℕ) :=
  let pad:=(head H lo).size
  if idx<pad then idx*chunks G M else
    if inside:idx-pad<B*chunks G M*2^(a*M) then
      let outer:=finProdFinEquiv.symm (⟨idx-pad,inside⟩ : Fin ((B*chunks G M)*2^(a*M)))
      let band:Fin B×Fin (chunks G M):=finProdFinEquiv.symm outer.1
      part 1 1 G M band.2 (table (M:=M) (pick band.1) outer.2)
    else 0

private theorem entry (H G M lo:ℕ) (b:Fin B) (j:Fin (chunks G M)) (z:Cell (a*M)) :
    literal H G M lo pick ((head H lo).size+(finProdFinEquiv (b,j)).val*2^(a*M)+z.val)=
      part 1 1 G M j (table (M:=M) (pick b) z) := by
  let pair:=finProdFinEquiv (b,j)
  let idx:=finProdFinEquiv (pair,z)
  have addr:(head H lo).size+pair.val*2^(a*M)+z.val=(head H lo).size+idx.val:=by
    change _=(head H lo).size+(z.val+2^(a*M)*pair.val)
    ring
  rw [show (finProdFinEquiv (b,j)).val=pair.val by rfl,addr]
  simp only [literal,show ¬(head H lo).size+idx.val<(head H lo).size by omega,ite_false,
    Nat.add_sub_cancel_left,dite_eq_left idx.isLt]
  change part 1 1 G M (finProdFinEquiv.symm (finProdFinEquiv.symm idx).1).2
    (table (M:=M) (pick (finProdFinEquiv.symm (finProdFinEquiv.symm idx).1).1) (finProdFinEquiv.symm idx).2)=_
  simp only [idx,pair,Equiv.symm_apply_apply]

theorem mapped {h g m:ℕ} (pick:Cell a→Cell 1) (zero:pick 0=0) (x:Fin h→Fin g→Cell a) (j:Row h g m) :
    table (M:=m) pick (data x j)=data (fun h g=>pick (x h g)) j := by
  unfold table data
  rw [Equiv.symm_apply_apply]
  congr 1
  funext k
  by_cases on:j.2.val*m+k.val<g <;> simp [Function.comp_apply,on,zero]

def field (H G M a lo:ℕ) (source:Fin B→Bank) (b:Fin B) (j:Fin (chunks G M)) : Expr :=
  .lookup (tableBank H G M a B lo b j) (.lookup (source b) (.op .add (.lookup (head H lo) .row) (.lit j.val)))
def emit (H G M a lo:ℕ) (source:Fin B→Bank) (b:Fin B) := total (field H G M a lo source b) (List.finRange (chunks G M))

section Run
variable (H G M lo:ℕ) (source:Fin B→Bank) (m:Memory w)
local notation "fee" => count H G M a B lo
local notation "high" => lo+fee
local notation "vals" => literal H G M lo pick
local notation "warm" => DescentStaticWordColumn.image lo vals m fee
local notation "rowExpr" => emit H G M a lo source
local notation "reads" => Gather.reads high H rowExpr

def program (w:ℕ) := (DescentStaticWordColumn.program w lo vals fee).seq (ProtocolRAM.program w reads)
def final := result reads warm
def ticks := (4+10*fee)+clock reads
def bank (b:Fin B) := Gather.banks high H b

private theorem fieldFits
    (before : ∀ b : Fin B, (source b).Fits w lo)
    (space : lo + count H G M a B lo + B * H < 2 ^ w)
    (b : Fin B) (j : Fin (chunks G M)) : (field H G M a lo source b j).Fits w high := by
  have limit : high < 2 ^ w := (Nat.le_add_right _ _).trans_lt space
  have fits (bank : Bank) (last : bank.base + bank.size ≤ high) : bank.Fits w high :=
    ⟨Nat.two_pow_pos _, (Nat.le_add_left _ _).trans_lt (last.trans_lt limit), last⟩
  have tableFits : (tableBank H G M a B lo b j).Fits w high := by
    apply fits
    have key := Nat.mul_le_mul_right (2 ^ (a * M)) (finProdFinEquiv (b, j)).isLt
    rw [Nat.succ_mul] at key
    change lo + (head H lo).size + (finProdFinEquiv (b, j)).val * 2 ^ (a * M) + 2 ^ (a * M) ≤
      lo + ((head H lo).size + (B * chunks G M) * 2 ^ (a * M))
    simpa only [Nat.add_assoc] using Nat.add_le_add_left (Nat.add_le_add_left key (head H lo).size) lo
  have headFits : (head H lo).Fits w high :=
    fits _ (Nat.add_le_add_left (Nat.le_add_right _ _) lo)
  have oldFits := before b
  exact ⟨tableFits, ⟨⟨oldFits.1, oldFits.2.1, oldFits.2.2.trans (Nat.le_add_right _ _)⟩,
    ⟨⟨headFits, trivial⟩, trivial⟩⟩⟩

private theorem sum_read {I:Type} (f:I→Expr) (value:I→ℕ) (mem:Memory w) (i:Word w)
    (hit:∀j,(f j).eval mem i=(value j:Word w)) (xx:List I) :
    (total f xx).eval mem i=((xx.map value).sum:Word w) := by
  induction xx with
  | nil=>rfl
  | cons j xs ih=>simp [total,Expr.eval,RowOp.opcode,BinaryOp.eval,hit,ih]

theorem any_raw
    (before : ∀ b : Fin B, (source b).Fits w lo)
    (space : lo + count H G M a B lo + B * H < 2 ^ w) :
    (program pick H G M lo source w).Exec m (final pick H G M lo source m) (ticks (a:=a) H G M lo source) ∧
    CheapCode (program pick H G M lo source w) ∧
    ∀idx,idx < lo ∨ high+B*H ≤ idx→final pick H G M lo source m idx=m idx := by
  have limit:high<2^w:=(Nat.le_add_right ..).trans_lt space
  have mount : (DescentStaticWordColumn.program w lo vals fee).Exec m warm (4 + 10 * fee) :=
    @DescentStaticWordColumn.mount w lo fee vals m limit
  have keep:=DescentStaticWordColumn.frame lo fee vals m
  have fits (b): (rowExpr b).Fits w high:=fits_total _ (fieldFits H G M lo source before space b) _
  have got:=Gather.fetch high H rowExpr warm fits space
  refine ⟨mount.then got.1,cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) got.2.1,?_⟩
  intro j away
  have later:lo≤high:=Nat.le_add_right ..
  exact (got.2.2.2 j (by rcases away with h|h <;> omega)).trans (keep _ (by rcases away with h|h <;> omega))

theorem issued
    (before : ∀ b : Fin B, (source b).Fits w lo)
    (length : ∀ b : Fin B, H * chunks G M ≤ (source b).size)
    (space : lo + count H G M a B lo + B * H < 2 ^ w)
    (zero:∀b,pick b 0=0) (hm:0<M)
    (raw:Fin B→Fin H→Fin G→Cell a) (old:∀b,∀j:Row H G M,
      m ((source b).base+(row H G M j).val)=((data (raw b) j).val:Word w)) :
    (program pick H G M lo source w).Exec m (final pick H G M lo source m) (ticks (a:=a) H G M lo source) ∧
    CheapCode (program pick H G M lo source w) ∧
    (∀b h,final pick H G M lo source m ((bank (a:=a) H G M lo b).base+h.val)=
      ((encode 1 G (fun g=>pick b (raw b h g))).val:Word w)) ∧
    ∀idx,idx<lo ∨ high+B*H≤ idx→final pick H G M lo source m idx=m idx := by
  have limit:high<2^w:=(Nat.le_add_right ..).trans_lt space
  have mount : (DescentStaticWordColumn.program w lo vals fee).Exec m warm (4 + 10 * fee) :=
    @DescentStaticWordColumn.mount w lo fee vals m limit
  have keep:=DescentStaticWordColumn.frame lo fee vals m
  have fits (b): (rowExpr b).Fits w high:=fits_total _ (fieldFits H G M lo source before space b) _
  have got:=Gather.fetch high H rowExpr warm fits space
  refine ⟨mount.then got.1,cheap_seq (@DescentStaticWordColumn.cheap _ _ _ _) got.2.1,?_,?_⟩
  · intro b h
    let x:=fun i g=>pick b (raw b i g)
    have curr (j:Fin (chunks G M)): (field H G M a lo source b j).eval warm (h.val:Word w)=
        (part 1 1 G M j (data x (h,j)):Word w) := by
      have bounds:=fieldFits H G M lo source before space b j
      have lh:h.val<(head H lo).size:=h.isLt.trans_le (Nat.le_pow_clog (by decide) _)
      have rootRead: (head H lo).read warm (h.val:Word w)=((h.val*chunks G M:ℕ):Word w):=by
        rw [DescentPackedZip.bank_read _ _ lh bounds.2.2.1.1]
        change warm (lo+h.val)=_
        have inRange:h.val<fee:=by unfold count;omega
        rw [DescentStaticWordColumn.read lo fee vals m inRange]
        simp [literal,lh]
      have rowVal:(row H G M (h,j)).val=h.val*chunks G M+j.val:=by simp [row,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]
      have okRow: (row H G M (h,j)).val<(source b).size:=(row H G M (h,j)).isLt.trans_le (length b)
      have original:=(DescentPackedZip.bank_read (source b) warm okRow (before b)).trans
        ((keep _ (.inl ((Nat.add_lt_add_left okRow _).trans_le (before b).2.2))).trans (old b (h,j)))
      let word:=data (raw b) (h,j)
      have key:=DescentPackedZip.bank_read (tableBank H G M a B lo b j) warm word.isLt bounds.1
      have cost: (finProdFinEquiv (b,j)).val*2^(a*M)+word.val<(B*chunks G M)*2^(a*M):=by
        have valid:=(finProdFinEquiv (finProdFinEquiv (b,j),word)).isLt
        simpa only [finProdFinEquiv_apply_val,Nat.mul_comm (2^(a*M)),Nat.add_comm word.val] using valid
      have atTable:warm ((tableBank H G M a B lo b j).base+word.val)=
          (part 1 1 G M j (table (M:=M) (pick b) word):Word w):=by
        change warm (lo+(head H lo).size+(finProdFinEquiv (b,j)).val*2^(a*M)+word.val)=_
        rw [show lo+(head H lo).size+(finProdFinEquiv (b,j)).val*2^(a*M)+word.val=
            lo+((head H lo).size+(finProdFinEquiv (b,j)).val*2^(a*M)+word.val) by omega,
          DescentStaticWordColumn.read lo fee vals m (by unfold count;omega),entry]
      have words:table (M:=M) (pick b) word=data x (h,j):=mapped _ (zero b) (raw b) _
      change (tableBank H G M a B lo b j).read warm
        ((source b).read warm ((head H lo).read warm (h.val : Word w) + (j.val : Word w))) = _
      rw [rootRead, ←Nat.cast_add, ←rowVal, original]
      exact (key.trans atTable).trans (congrArg (fun z=>(part 1 1 G M j z:Word w)) words)
    have sum:=sum_read (field H G M a lo source b) (fun j=>part 1 1 G M j (data x (h,j))) warm
      (h.val:Word w) curr (List.finRange (chunks G M))
    rw [←List.ofFn_eq_map,List.sum_ofFn] at sum
    have packed:=DescentTerminalPopulation.packed (M:=M) x (fun _=>0) 1 hm (fun h g=>by simpa using (x h g).isLt) h
    simp only [words,common,Nat.mul_zero,Finset.sum_const_zero,Nat.zero_add] at packed
    exact (got.2.2.1 b h).trans (sum.trans (congrArg (fun z:ℕ=>(z:Word w)) packed))
  · intro j away
    exact (got.2.2.2 j (by rcases away with h|h <;> omega)).trans (keep _ (by rcases away with h|h <;> omega))

theorem price : ticks (a:=a) H G M lo source≤
    8+10*fee+B*(4+H*(6+52*chunks G M)) := by
  have bounded (b:Fin B): (rowExpr b).work≤1+26*chunks G M:=by
    have bill:=work_total (field H G M a lo source b) 25 (fun j=>by simp [field,Expr.work]) (List.finRange (chunks G M))
    simpa only [emit,List.length_finRange,show (25:ℕ)+1=26 by decide,Nat.mul_comm (chunks G M) 26] using bill
  have bill:=Gather.fetch_price rowExpr (1+26*chunks G M) high H bounded
  unfold ticks
  convert Nat.add_le_add_left bill (4+10*fee) using 1; ring
end Run

def blockBit (b:Fin B) (word:Cell (1*B)) : Cell 1 := (encode 1 B).symm word b
theorem blockBit_zero (b:Fin B) : blockBit b 0=0 := by
  have zero:(encode 1 B (fun _=>0 : Fin B→Cell 1))=0:=by apply Fin.ext;simp [encode]
  rw [←zero,blockBit,Equiv.symm_apply_apply]

theorem actual {U V:Type} [Fintype U] [DecidableEq V] {k:ℕ} (home:U→V) (block:U→Fin (2^k))
    (v:V) (b:Fin (2^k)) : (blockBit b (DescentActorRaster.actorMask home block v)).val=
      if ∃u,home u=v ∧ block u=b then 1 else 0 := by
  rw [blockBit,DescentActorRaster.actorMask,Equiv.symm_apply_apply]
  exact (digit_encode (DescentActorRaster.present home block v) b).symm.trans (DescentActorRaster.actor_read home block v b)

end
end Hierarchy.DescentTerminalActorRepack

end OAI
