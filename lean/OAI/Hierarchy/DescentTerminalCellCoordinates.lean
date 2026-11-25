import OAI.Hierarchy.DescentTerminalCohortSize
import OAI.Hierarchy.DescentSIMDEncodedPin
import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Reading fields of a terminal row from the measured block and family banks -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentSIMDLookup DescentSixParty.PackedCensus
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {q t H N A w groups blocks : ℕ}
local notation "sized" => familySize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w)
local notation "Venue" => (f : Fin 8)→Word (sized f)

section
local notation "K" => Key H N A
local notation "len" => bits q t H N A w

/-- The eight shelves are public arities, the constant singleton marker, hidden and
node counts, private widths, roles, node arities, and concrete public/private pointers. -/
def group : K→Fin 8
  | .inl _=>0
  | .inr (.inl _)=>1
  | .inr (.inr (.inl _))=>2
  | .inr (.inr (.inr (.inl _)))=>3
  | .inr (.inr (.inr (.inr (.inl _))))=>4
  | .inr (.inr (.inr (.inr (.inr (.inl _)))))=>5
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl _))))))=>6
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr _))))))=>7

def item : (k : K) → Fin (items H N A (group k))
  | .inl _=> (0 : Fin 1)
  | .inr (.inl _)=> (0 : Fin 1)
  | .inr (.inr (.inl _))=> (0 : Fin 1)
  | .inr (.inr (.inr (.inl _)))=> (0 : Fin 1)
  | .inr (.inr (.inr (.inr (.inl z))))=>z.2
  | .inr (.inr (.inr (.inr (.inr (.inl z)))))=>z.2
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl z))))))=>z.2
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr z))))))=>finProdFinEquiv z.2

theorem item_len (k : K) : len k=itemBits q t H N A w (group k) := by
  rcases k with _|(_|(_|(_|(_|(_|(_|_)))))) <;> rfl

def within (k : K) (j : Fin (len k)) : Fin (sized (group k)) :=
  finProdFinEquiv (item k,j.cast (item_len k))

end

abbrev BlockFields (q t H N A w groups blocks : ℕ) :=
  (j : Fin (channels blocks))→Word (channelSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (groups:=groups) j)
local notation "Inputs" => BlockFields q t H N A w groups blocks

def blankAt (data : Inputs) (c : Fin (groups*blocks)) : Word 1 :=
  let gb:=finProdFinEquiv.symm c
  (encode 1 groups).symm ((data (finProdFinEquiv (gb.2,(0:Fin 9)))).cast (by simp [channelSize,primitiveSize])) gb.1

def cellAt (data : Inputs) (c : Fin (groups*blocks)) : Venue := fun f=>
  let gb:=finProdFinEquiv.symm c
  (encode (sized f) groups).symm ((data (finProdFinEquiv (gb.2,f.succ))).cast (by simp [channelSize,primitiveSize])) gb.1

theorem presence_digit (data : Inputs) (g : Fin groups) (b : Fin blocks) :
    (blankAt data (finProdFinEquiv (g,b))).val=digit 1 g.val (data (finProdFinEquiv (b,(0:Fin 9)))).val := by
  let read (gb : Fin groups × Fin blocks) : Word 1 :=
    (encode 1 groups).symm ((data (finProdFinEquiv (gb.2,(0:Fin 9)))).cast
      (by simp [channelSize,primitiveSize])) gb.1
  change (read (finProdFinEquiv.symm (finProdFinEquiv (g,b)))).val=_
  rw [Equiv.symm_apply_apply]
  have h:=digit_encode ((encode 1 groups).symm ((data (finProdFinEquiv (b,(0:Fin 9)))).cast (by simp [channelSize,primitiveSize]))) g
  simpa [read] using h.symm

theorem cell_digit (data : Inputs) (g : Fin groups) (b : Fin blocks) (f : Fin 8) :
    (cellAt data (finProdFinEquiv (g,b)) f).val=digit (sized f) g.val (data (finProdFinEquiv (b,f.succ))).val := by
  let read (gb : Fin groups × Fin blocks) : Word (sized f) :=
    (encode (sized f) groups).symm ((data (finProdFinEquiv (gb.2,f.succ))).cast
      (by simp [channelSize,primitiveSize])) gb.1
  change (read (finProdFinEquiv.symm (finProdFinEquiv (g,b)))).val=_
  rw [Equiv.symm_apply_apply]
  have h:=digit_encode ((encode (sized f) groups).symm ((data (finProdFinEquiv (b,f.succ))).cast (by simp [channelSize,primitiveSize]))) g
  simpa [read] using h.symm

structure MaskedShelf (blocks : ℕ) where
  channel : Fin (channels blocks)→Bank
  weight : Fin (channels blocks)→Bank
  table : Bank

section
variable {bits S : ℕ}

def measured (L : MaskedShelf blocks) (mem : Memory bits) (i : Fin S) : Inputs :=
  fun f=>((L.channel f).read mem (i.val:Word bits)).val

end

def venueField (v : Venue) (k : Key H N A) :=
  ((wordBits (bits q t H N A w k)).symm (fun j=>wordBits _ (v (group k)) (within k j))).val

local notation "lengths" => itemBits q t H N A w
abbrev PrimitiveFields (q t H N A w : ℕ) :=
  (f:Fin 8)→Fin (items H N A f)→Word (itemBits q t H N A w f)
local notation "Fields" => PrimitiveFields q t H N A w

def panelWord (x : Fields) (f:Fin 8) : Word (sized f) :=
  (encode (lengths f) (items H N A f) (x f)).cast (by rw [familySize,Nat.mul_comm])

theorem panelField (x : Fields) (k : Key H N A) : venueField (panelWord x) k=(x (group k) (item k)).val := by
  let answer : Word (bits q t H N A w k) :=
    (x (group k) (item k)).cast (congrArg (2^·) (item_len (q:=q) (t:=t) (w:=w) k).symm)
  change ((wordBits _).symm _).val=answer.val
  apply congrArg Fin.val
  apply (wordBits _).injective
  rw [Equiv.apply_symm_apply]
  funext j
  simp only [←Computability.VPVNP.LiveHeader.testBit_wordBits]
  exact encode_pin (x (group k)) (item k) (j.cast (item_len k))

local notation "len" => itemBits q t H N A w

def unpack (v : Venue) : PrimitiveFields q t H N A w := fun f=>
  (encode (len f) (items H N A f)).symm ((v f).cast (by rw [familySize,Nat.mul_comm]))

theorem pack_unpack (v:Venue) : panelWord (unpack v)=v := by
  funext f
  apply Fin.ext
  simp only [panelWord,unpack,Fin.val_cast,Equiv.apply_symm_apply]

theorem venue_digit (v:Venue) (k:Key H N A) :
    venueField v k=digit (len (group k)) (item k).val (v (group k)).val := by
  have word:=panelField (unpack v) k
  rw [pack_unpack] at word
  have stored:=(digit_encode (unpack v (group k)) (item k)).symm
  simp only [unpack,Equiv.apply_symm_apply,Fin.val_cast] at stored
  exact word.trans stored


end
end Hierarchy.DescentTerminalVertexFields

end OAI
