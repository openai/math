import OAI.Hierarchy.DescentPackedMaskedData
import OAI.Hierarchy.DescentResetLocalOverflow
import OAI.Hierarchy.DescentPackedResetImage
import OAI.Hierarchy.DescentPackedSplitContribution
import OAI.Hierarchy.DescentFallbackShapeTable

namespace OAI
/-! # A single shared packed lookup for the selected reset leaf shape and exceptional bit -/

namespace Hierarchy.DescentPlainTerminal.Suffix.Stencil
open DescentColonies DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentPackedFallbackTree.Image
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {r n q t w H G M : ℕ}

/-- Three header fields, old weights, split votes, old-order comparisons, and one
directed flow aperture per incoming or outgoing port. -/
abbrev Slot (r q : ℕ) := Fin 3 ⊕ ((Block r ⊕ (Fin r × Block r)) ⊕
  ((Block r × Block r) ⊕ (Fin q × (Fin 2 ⊕ Block r))))
abbrev panel (r q n : ℕ) := Slot r q → Cell n
def count (r q : ℕ) := Fintype.card (Slot r q)
def pack (r q n : ℕ) : panel r q n ≃ Cell (n*count r q) :=
  (Equiv.arrowCongr (Fintype.equivFin _) (Equiv.refl _)).trans (encode n _)

theorem count_eq (r q : ℕ) : count r q=3+(2^r+r*2^r+(2^r*2^r+q*(2+2^r))) := by
  simp [count,Slot,Fintype.card_sum,Fintype.card_prod]

def header (a : panel r q n) (i : Fin 3) := (a (.inl i)).val
def old (a : panel r q n) (x : Block r) := (a (.inr (.inl (.inl x)))).val
def marked (a : panel r q n) (d : Fin r) (x : Block r) := decide ((a (.inr (.inl (.inr (d,x))))).val≠0)
def before (a : panel r q n) (i x : Block r) := decide ((a (.inr (.inr (.inl (i,x))))).val≠0)
def edge (a : panel r q n) (p : Fin q) (x : Fin 2 ⊕ Block r) := (a (.inr (.inr (.inr (p,x))))).val

def fails (a : panel r q n) (x : Block r) : Prop :=
  ∃p : Fin q,∃i : Block r,group (header a 0) i=group (header a 0) x ∧
    edge a p (.inl 1)<binHere (fun y=>edge a p (.inr y)) (edge a p (.inl 0)) i

def split (a : panel r q n) (x : Block r) := DescentColonies.PackedSplit.depth (marked a) x
def bad (a : panel r q n) (x : Block r) := decide (header a 0<split a x ∨ fails a x)
def shape (a : panel r q n) (f B Y : ℕ) (x : Block r) := row (header a 0) (header a 1) f B Y
  (decide (header a 2≠0)) (bad a x) (before a) (split a) (old a) x

def shapeCode (r Y : ℕ) (y : (ℕ×ℕ)×Option ℕ) : ℕ :=
  (y.1.1*2^r+y.1.2)*(Y+1)+(y.2.elim 0 (·+1))

theorem shapeCode_fields (r : ℕ) {Y : ℕ} (z : DescentContacts.Endpoint Y) :
    shapeCode r Y (fields z)=DescentFallbackShapeTable.cell r z := by
  rcases z with ⟨⟨d,id⟩,_|j⟩ <;> rfl

def word (a : panel r q n) (f B Y : ℕ) (x : Block r) : ℕ :=
  2*shapeCode r Y (shape a f B Y x)+(decide (header a 2≠0) || bad a x).toNat

/-- Invalid and padding inputs are interpreted by the same fixed total lookup. -/
def lookup (r q n t f B Y : ℕ) (key : Cell (n*count r q)) : Cell (t*2^r) :=
  encode t (2^r) (fun x=>(word ((pack r q n).symm key) f B Y x:Cell t))

theorem lookup_read (a : panel r q n) (t f B Y : ℕ) (x : Block r) :
    digit t x.val (lookup r q n t f B Y (pack r q n a)).val=((word a f B Y x : ℕ):Cell t).val := by
  rw [lookup,digit_encode,Equiv.symm_apply_apply]

theorem compiled_words (r q n t f B Y : ℕ) (g : Banks) (out : ℕ) (positive : 0<M)
    (fit : Fits g (n*count r q) (t*2^r) M H G w out) (m : Memory w)
    (a : Fin H→Fin G→panel r q n) (rom : resident (lookup r q n t f B Y) g H G M m)
    (dataAt : ∀i : Row H G M,m (g.source.base+(DescentSIMDLookup.row H G M i).val)=
      ((data (fun v j=>pack r q n (a v j)) i).val:Word w)) :
    let dst:=imageBank H G M out g m
    (DescentSIMDLookup.program g out H G M w).Exec m dst (4+44*(H*chunks G M)) ∧
      (∀v j (x : Block r),digit t x.val (digit (t*2^r) (lane j positive).val
        (dst (out+(DescentSIMDLookup.row H G M (position v j positive)).val)).val)=((word (a v j) f B Y x:ℕ):Cell t).val) ∧
      (∀z<out,dst z=m z) ∧ (∀z,out+H*chunks G M≤z→dst z=m z) ∧
      ∀i : Row H G M,dst (out+(DescentSIMDLookup.row H G M i).val)=
        ((data (fun v j=>encode t (2^r) (fun x=>(word (a v j) f B Y x:Cell t))) i).val:Word w) := by
  let l:=lookup r q n t f B Y
  let inputs:=fun v j=>pack r q n (a v j)
  have frame : PinFrame (M:=M) g l inputs m := by
    refine ⟨?_,dataAt⟩
    intro key bit
    cases key with
    | inl i=>exact congrArg (fun z=>wordBits w z bit) (rom.1 i)
    | inr i=>exact congrArg (fun z=>wordBits w z bit) (rom.2 i)
  have ok : (DescentSIMDLookup.lookup g).Fits w out := ⟨⟨fit.dictionary,fit.source,trivial⟩,fit.mask,trivial⟩
  let dst:=imageBank H G M out g m
  have real (i : Row H G M) : dst (out+(DescentSIMDLookup.row H G M i).val)=(masked l inputs i:Word w):=
    (ProtocolRAMGeneratedWrite.read_image _ _ _ _ _).trans (DescentSIMDLookup.lookup_read g out fit l inputs m frame i)
  refine ⟨?_,?_,fun a ha=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl ha),
    fun a ha=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr ha),?_⟩
  · have charge : 2*(DescentSIMDLookup.lookup g).work+4 = 44 := rfl
    change (scan w out (H*chunks G M) (DescentSIMDLookup.lookup g)).Exec m
      (ProtocolRAM.image out (H*chunks G M) (DescentSIMDLookup.lookup g) m) _
    rw [Nat.mul_comm 44,←charge]
    intro pcCount regCount slotCount machine pcMap regMap pub exit installed romData cfg input entry same
    subst input
    exact scan_exec out (H*chunks G M) _ m ok fit.output machine pcMap regMap pub exit
      installed romData cfg m entry rfl
  · intro v j x
    rw [physical_read g out fit l inputs dst real v j positive]
    exact lookup_read (a v j) t f B Y x
  · intro i
    simpa only [DescentSIMDLookup.masked_eq_data,l,inputs,lookup,Equiv.symm_apply_apply] using real i

theorem compiled (r q n t f B Y : ℕ) (g : Banks) (out : ℕ) (positive : 0<M)
    (fit : Fits g (n*count r q) (t*2^r) M H G w out) (m : Memory w)
    (a : Fin H→Fin G→panel r q n) (rom : resident (lookup r q n t f B Y) g H G M m)
    (dataAt : ∀i : Row H G M,m (g.source.base+(DescentSIMDLookup.row H G M i).val)=
      ((data (fun v j=>pack r q n (a v j)) i).val:Word w)) :
    let dst:=imageBank H G M out g m
    (DescentSIMDLookup.program g out H G M w).Exec m dst (4+44*(H*chunks G M)) ∧
      (∀v j (x : Block r),digit t x.val (digit (t*2^r) (lane j positive).val
        (dst (out+(DescentSIMDLookup.row H G M (position v j positive)).val)).val)=((word (a v j) f B Y x:ℕ):Cell t).val) ∧
      (∀z<out,dst z=m z) ∧ ∀z,out+H*chunks G M≤z→dst z=m z := by
  obtain ⟨exe,real,lo,hi,_⟩:=compiled_words r q n t f B Y g out positive fit m a rom dataAt
  exact ⟨exe,real,lo,hi⟩

end
end Hierarchy.DescentPlainTerminal.Suffix.Stencil

end OAI
