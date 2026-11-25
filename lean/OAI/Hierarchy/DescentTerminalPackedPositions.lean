import OAI.Hierarchy.DescentTerminalClippedFields

namespace OAI
/-! # Consecutive genuinely occupied vertices across short packed predecessor shelves -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentTerminalDenseWindow DescentTerminalDenseHeader DescentKernelHistory
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators
noncomputable section
variable {q t H N A w V M S B : ℕ}
local notation "width" => span q t H N A w
local notation "sized" => familySize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w)
local notation "Group" => Panels (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) M
local notation "Rows" => Panels (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) V
local notation "Raw" => Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)

def streamBit (stream : ℕ→Group) (mp : 0<M) (v : ℕ) (f : Fin 8) (j : Fin (sized f)) :=
  wordBits _ (stream (v/M) f) (finProdFinEquiv (⟨v%M,Nat.mod_lt _ mp⟩,j))

/-- Every source venue occupies a short rectangle in its own family. The two
adjacent source batches suffice even when the first sibling is the last venue in a batch. -/
def joinGroups (enough : V≤M) (skip : Fin M) (lo hi : Group) : Rows := fun f=>
  (wordBits _).symm fun i=>
    let vb:Fin V×Fin (sized f):=finProdFinEquiv.symm i
    let n:=skip.val+vb.1.val
    if hr:n<M then wordBits _ (lo f) (finProdFinEquiv (⟨n,hr⟩,vb.2))
    else wordBits _ (hi f) (finProdFinEquiv (⟨n-M,by have:=skip.isLt;have:=vb.1.isLt;dsimp [n];omega⟩,vb.2))

theorem join_read (stream : ℕ→Group) (mp : 0<M) (wide : V≤M) (start : ℕ) (v : Fin V) (f : Fin 8) (j : Fin (sized f)) :
    wordBits _ (joinGroups wide ⟨start%M,Nat.mod_lt _ mp⟩ (stream (start/M)) (stream (start/M+1)) f) (finProdFinEquiv (v,j))=
      streamBit stream mp (start+v.val) f j := by
  let r:=start%M+v.val
  have first:=Nat.div_add_mod start M
  have small:=Nat.mod_lt start mp
  have vr:=v.isLt
  simp only [joinGroups,Equiv.apply_symm_apply,Equiv.symm_apply_apply]
  change (if hr:r<M then _ else _)=_
  by_cases inside:r<M
  · rw [dite_eq_left inside]
    have a : start+v.val=M*(start/M)+r := by dsimp [r];omega
    simp [streamBit,a,Nat.mul_add_div mp,Nat.div_eq_of_lt inside,Nat.mod_eq_of_lt inside]
    rfl
  · rw [dite_eq_right inside]
    have next : r-M<M := by dsimp [r];omega
    have a : start+v.val=M*(start/M+1)+(r-M) := by rw [Nat.mul_add,Nat.mul_one];dsimp [r] at *;omega
    simp [streamBit,a,Nat.mul_add_div mp,Nat.div_eq_of_lt next,Nat.mod_eq_of_lt next]
    rfl

def population (books : Fin S→Raw) (i : ℕ) := pref (fun k=>(books k).1.val) i
def popProfile (books : Fin S→Raw) (wide : V≤M) (i : Fin S) : Profile 1 M :=
  fun _=>⟨(books i).1.val,(books i).1.isLt.trans_le (Nat.succ_le_succ wide)⟩
theorem pop_prefix (books : Fin S→Raw) (wide : V≤M) (i : ℕ) :
    priorBits (popProfile books wide) i=population books i := by
  simp [priorBits,population,mass,slotPrefix,pref,lengthAt,popProfile]

def siblings (books : Fin S→Raw) (wide : V≤M) (mp : 0<M) (stream : ℕ→Group) (i : Fin S) : Rows :=
  let n:=population books i.val
  joinGroups wide ⟨n%M,Nat.mod_lt _ mp⟩ (stream (n/M)) (stream (n/M+1))

def groupField (stream : ℕ→Group) (mp : 0<M) (v : ℕ) (k : Key H N A) :=
  ((wordBits (bits q t H N A w k)).symm (fun j=>streamBit stream mp v (group k) (within k j))).val

theorem raw_sibling (books : Fin S→Raw) (wide : V≤M) (mp : 0<M) (stream : ℕ→Group) (i : Fin S)
    (v : Fin V) (k : Key H N A) :
    raw (siblings books wide mp stream i) v k=groupField stream mp (population books i.val+v.val) k := by
  unfold raw groupField
  congr 2
  funext j
  exact join_read stream mp wide _ v _ _

theorem siblings_source (books : Fin S→Raw) (stream : ℕ→Group) (wide : V≤M) (mp : 0<M) (fit : V*width≤B) (bp : 0<B)
    (zero : ∀i v,Zeros ((books i).2 v))
    (issued : ∀i (v : Fin (books i).1.val) k,allows (fun a=>(value ((books i).2 v) a).val) k→
      groupField stream mp (population books i.val+v.val) k=(value ((books i).2 v) k).val) (i : Fin S) :
    Source (books i) (i.val*B) (bitsAt (fun a=>clippedPage (siblings books wide mp stream a) fit) bp) := by
  apply clipped_source books (siblings books wide mp stream) fit bp zero _ i
  intro a v k live
  rw [raw_sibling]
  exact issued a v k live

end
end Hierarchy.DescentTerminalVertexFields

end OAI
