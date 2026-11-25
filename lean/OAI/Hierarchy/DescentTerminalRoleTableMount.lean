import OAI.Hierarchy.DescentTerminalRoleShelfData
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Installing the six shared shifts and both scalar-role output tables once -/
namespace Hierarchy.DescentTerminalRoleTables
open DescentTerminalVertexFields DescentEpochTagKeys DescentTerminalCombinedRole DescentSIMDLookup ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators Fin.CommRing
noncomputable section

def marks (bits:Fin 6→ℕ) := ∑f,2^(bits f)
def «prefix» (bits:Fin 6→ℕ) (f:Fin 6) := ∑j:Fin f.val,2^(bits (j.castLE f.isLt.le))
def menus (bits:Fin 6→ℕ) := ∏f,2^(bits f)
def count (bits:Fin 6→ℕ) := marks bits+menus bits+menus bits
def Keys (bits:Fin 6→ℕ) := ((Σf:Fin 6,Fin (2^(bits f))) ⊕ Fin (menus bits)) ⊕ Fin (menus bits)
def ordinal (bits:Fin 6→ℕ) : Keys bits≃Fin (count bits) :=
  (((finSigmaFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv).sumCongr (Equiv.refl _)).trans finSumFinEquiv

private theorem shift_at (bits:Fin 6→ℕ) (f:Fin 6) (j:Fin (2^(bits f))) :
    (ordinal bits (.inl (.inl ⟨f,j⟩))).val=«prefix» bits f+j.val := by
  change (finSigmaFinEquiv (n:=fun i:Fin 6=>2^(bits i)) ⟨f,j⟩).val = _
  exact finSigmaFinEquiv_apply _
private theorem role_at (bits:Fin 6→ℕ) (j:Fin (menus bits)) :
    (ordinal bits (.inl (.inr j))).val=marks bits+j.val := by rfl
private theorem arity_at (bits:Fin 6→ℕ) (j:Fin (menus bits)) :
    (ordinal bits (.inr j)).val=marks bits+menus bits+j.val := by rfl

def role (bits:Fin 6→ℕ) (input:Fin 6→Bank) (base:ℕ) : Shelf where
  input := input
  shift f := ⟨base+«prefix» bits f,bits f⟩
  menu := ⟨base+marks bits,∑f,bits f⟩
def arity (bits:Fin 6→ℕ) (input:Fin 6→Bank) (base:ℕ) : Shelf :=
  {role bits input base with menu:=⟨base+marks bits+menus bits,∑f,bits f⟩}

theorem fits (bits:Fin 6→ℕ) (input:Fin 6→Bank) (base out wb:ℕ)
    (sources:∀f,(input f).Fits wb out) (later:base+count bits≤out) (limit:out<2^wb) :
    (emit (role bits input base)).Fits wb out ∧ (emit (arity bits input base)).Fits wb out := by
  have capacity:menus bits=2^(∑f:Fin 6,bits f):=by unfold menus;rw [Finset.prod_pow_eq_pow_sum]
  have menuFit (start:ℕ) (bound:start+menus bits≤out) : (⟨start,∑f,bits f⟩:Bank).Fits wb out := by
    refine ⟨Nat.two_pow_pos _,?_,?_⟩
    · change 2^(∑f,bits f)<2^wb;rw [←capacity];omega
    · simpa only [Bank.size,←capacity] using bound
  have shiftFit (f:Fin 6) : ((role bits input base).shift f).Fits wb out := by
    let j:Fin (2^(bits f)):=⟨2^(bits f)-1,by have:=Nat.two_pow_pos (bits f);omega⟩
    have pos:0<2^(bits f):=Nat.two_pow_pos _
    have bound:«prefix» bits f+j.val< marks bits:=by
      simpa only [finSigmaFinEquiv_apply,«prefix»,marks] using
        (finSigmaFinEquiv (n:=fun j:Fin 6=>2^(bits j)) ⟨f,j⟩).isLt
    have end_:«prefix» bits f+2^(bits f)≤ marks bits:=by dsimp only [j] at bound;omega
    unfold count at later
    exact ⟨pos,by change 2^(bits f)<_;omega,by change base+«prefix» bits f+2^(bits f)≤_;omega⟩
  have more (xs:List (Fin 6)) : (sumExpr (term (role bits input base)) xs).Fits wb out := by
    induction xs with
    | nil=>trivial
    | cons j tail ih=>exact ⟨⟨shiftFit j,sources j,trivial⟩,ih⟩
  unfold count at later
  exact ⟨⟨menuFit _ (by omega),more _⟩,⟨menuFit _ (by omega),more _⟩⟩

variable {U:Type} {n A G p R N groups wb:ℕ} (old:Codec U n) (slots:ℕ)
local notation "field" => fun f:Fin 6=>width n A G p R f*N*groups
local notation "raw" => Sources n A G p R N groups
def value : Keys field→ℕ
  | .inl (.inl ⟨f,j⟩)=>scale (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) f*j.val
  | .inl (.inr j)=>(rolePanel old (finPiFinEquiv.symm j:raw)).val
  | .inr j=>(countPanel slots (finPiFinEquiv.symm j:raw)).val
def literal (j:ℕ) :=
  if h:j<count field then value (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (groups:=groups) old slots ((ordinal field).symm ⟨j,h⟩) else 0
local notation "rom" => literal (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (groups:=groups) old slots
variable (input:Fin 6→Bank) (base:ℕ) (m:Memory wb)
local notation "next" => DescentStaticWordColumn.image base rom m (count field)
local notation "installed" => DescentStaticWordColumn.program wb base rom (count field)
local notation "f5" => role field input base
local notation "f6" => arity field input base

theorem mounted (room:base+count (fun f:Fin 6=>DescentTerminalCombinedRole.width n A G p R f*N*groups)<2^wb) :
    (installed).Exec m next (4+10*count field) ∧ CheapCode installed ∧
    Static (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) old f5 next ∧
    CountStatic (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) slots f6 next ∧
    ∀j,j<base ∨ base+count field≤j→next j=m j := by
  have read (k:Keys field) : next (base+(ordinal field k).val)=(value old slots k:Word wb) := by
    simpa only [literal,dite_eq_left (ordinal field k).isLt,Fin.eta,Equiv.symm_apply_apply] using
      DescentStaticWordColumn.read base (count field) rom m (ordinal field k).isLt
  have capacity:menus field=2^(∑f:Fin 6,field f):=by unfold menus;rw [Finset.prod_pow_eq_pow_sum]
  have key:menus field≤2^wb:=
    (Nat.le_add_left (menus field) (marks field+menus field)).trans ((Nat.le_add_left (count field) base).trans room.le)
  have shifts (f:Fin 6) (j:Fin (2^(field f))) :
      next (base+«prefix» field f+j.val)=(scaleWords (wb:=wb) (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) f)[j] := by
    have h:=read (.inl (.inl ⟨f,j⟩));rw [shift_at] at h
    simpa [value,scaleWords,Nat.add_assoc] using h
  refine ⟨DescentStaticWordColumn.mount base (count field) rom m room,@DescentStaticWordColumn.cheap wb base rom (count field),?_,?_,DescentStaticWordColumn.frame base (count field) rom m⟩
  · refine ⟨fun _=>rfl,shifts,capacity.le,key,?_⟩
    intro j
    have h:=read (.inl (.inr j))
    change next (base+(marks field+j.val))=_ at h
    simpa [role,value,menuWords,Nat.add_assoc] using h
  · refine ⟨fun _=>rfl,shifts,capacity.le,key,?_⟩
    intro j
    have h:=read (.inr j)
    change next (base+(marks field+menus field+j.val))=_ at h
    simpa [arity,value,countWords,Nat.add_assoc] using h

/-- The global initializer can run before the descent.  No source bank is read
during mounting.  All later geometry may change above the fixed ROM segment. -/
theorem persistent (room:base+count (fun f:Fin 6=>DescentTerminalCombinedRole.width n A G p R f*N*groups)<2^wb) (later:Memory wb) (retained:∀j,base≤j→j<base+count field→later j=next j) :
    Static (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) old f5 later ∧
    CountStatic (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) slots f6 later := by
  have mounted_:=mounted (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (groups:=groups) old slots input base m room
  let roleRead:=mounted_.2.2.1
  let countRead:=mounted_.2.2.2.1
  have shift (f:Fin 6) (j:Fin (2^(field f))) : later (base+«prefix» field f+j.val)=next (base+«prefix» field f+j.val) := by
    apply retained <;> try omega
    have bound:«prefix» field f+j.val< marks field:=by
      simpa only [finSigmaFinEquiv_apply,«prefix»,marks] using
        (finSigmaFinEquiv (n:=fun f:Fin 6=>2^(field f)) ⟨f,j⟩).isLt
    unfold count;omega
  have r (j:Fin (menus field)):later (base+marks field+j.val)=next (base+marks field+j.val):=by
    have length:=j.isLt
    apply retained
    · omega
    · unfold count;omega
  have a (j:Fin (menus field)):later (base+marks field+menus field+j.val)=next (base+marks field+menus field+j.val):=by
    have length:=j.isLt
    apply retained
    · omega
    · unfold count;omega
  exact ⟨⟨roleRead.radix,fun f j=>(shift f j).trans (roleRead.shift f j),roleRead.slots,roleRead.key,
    fun j=>(r j).trans (roleRead.dictionary j)⟩,
    ⟨countRead.radix,fun f j=>(shift f j).trans (countRead.shift f j),countRead.capacity,countRead.key,
    fun j=>(a j).trans (countRead.table j)⟩⟩

theorem price {h:ℕ} (fit:(∑f:Fin 6,field f)+3≤h/2) : count field≤2^(h/2) :=
  combined_advice (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) h fit

end
end Hierarchy.DescentTerminalRoleTables

end OAI
