import OAI.Hierarchy.DescentResetRetainedPages

namespace OAI
/-! # The retained summand of each reset pointer field, including all three spans -/
namespace Hierarchy.DescentResetRetainedPages
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM DescentOperandStateBanks
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {s t H G M w : ℕ}

/-- The exterior ticket and its original aligned chunk come from the exact
old bank, and the three range fields survive for all operand kinds. -/
def oldPart (f : Field) (tag earlier : Cell s) : Cell s :=
  if 4≤f.val ∨ tag.val=2 then earlier else 0

/-- One-based renaming distinguishes a real first slot from a vacant cell. -/
def aliasPart (f : Field) (tag : Cell s) (old : Cell t) : Cell s :=
  if f.val=2 ∧ tag.val=0 then ((old.val-1:ℕ):Cell s) else 0

def kept (f : Field) (tag earlier : Cell s) (alias_ : Cell t) : Cell s :=
  if 4≤f.val ∨ tag.val=2 then earlier else aliasPart f tag alias_

theorem pieces (f : Field) (t₀ x : Cell s) (y : Cell t) :
    (kept f t₀ x y).val=(oldPart f t₀ x).val+(aliasPart f t₀ y).val :=by
  by_cases h : 4≤f.val ∨ t₀.val=2
  · have d : ¬(f.val=2 ∧ t₀.val=0):=by omega
    simp only [kept, oldPart, aliasPart, ite_eq_left h, ite_eq_right d, Fin.val_zero, Nat.add_zero]
  · simp [kept,oldPart,h]

theorem ghost (f : Field) : kept f (0:Cell s) 0 (0:Cell t)=0 :=by simp [kept,aliasPart]

theorem pin (x : Field→Cell s) (a q : ℕ) (span : Span) (label : Cell t)
    (old : ∀f,(x f).val=(Pointer.pin a q).fields span f) (f : Field) :
    (kept f (x 0) (x f) label).val=(Pointer.pin a q).fields span f :=by
  have tag : (x 0).val=2:=old 0
  simp only [kept,tag,or_true,ite_true];exact old f

theorem hidden (x : Field→Cell s) (a b : ℕ) (span : Span) (label : Cell t)
    (old : ∀f,(x f).val=(Pointer.privateWord a).fields span f) (relabel : label.val=b+1) (room : b<2^s) (f : Field) :
    (kept f (x 0) (x f) label).val=(Pointer.privateWord b).fields span f :=by
  have tag : (x 0).val=0:=old 0
  fin_cases f <;> simp [kept,aliasPart,tag,old,relabel,Nat.mod_eq_of_lt room,Pointer.fields,Pointer.header]

theorem cable (x : Field→Cell s) (peer name chunk : ℕ) (span : Span) (label : Cell t)
    (old : ∀f,(x f).val=(Pointer.cable peer name chunk).fields span f) (f : Field) :
    (kept f (x 0) (x f) label).val=if f.val<4 then 0 else (Pointer.cable peer name chunk).fields span f :=by
  have tag : (x 0).val=1:=old 0
  by_cases first : f.val<4
  · simp [kept,aliasPart,tag,first,Nat.not_le.mpr first]
  · simp [kept,show 4≤f.val by omega,first,old]

def header (oldTable aliasTable : Tables) (_f : Field) (tag earlier ali : Expr) : Expr :=
  .op .add (oldTable.read tag earlier) (aliasTable.read tag ali)

theorem header_source (left right : Tables) (f : Field) (tag old ali : Expr) (cut : ℕ) (m : Memory w)
    (t₀ x : Fin H→Fin G→Cell s) (y : Fin H→Fin G→Cell t)
    (fit1 : DescentPackedZip.Fits left tag old s s M cut w) (fit2 : DescentPackedZip.Fits right tag ali s t M cut w)
    (ltab : Static left (oldPart (s:=s) f) M m) (rtab : Static right (aliasPart (s:=s) (t:=t) f) M m)
    (tr : Source tag t₀ M m) (oread : Source old x M m) (ar : Source ali y M m) :
    Source (header left right f tag old ali) (fun h g=>kept f (t₀ h g) (x h g) (y h g)) M m :=by
  have l:=read_data left tag old cut fit1 (oldPart f) (by simp [oldPart]) m ltab t₀ x tr oread
  have r:=read_data right tag ali cut fit2 (aliasPart f) (by simp [aliasPart]) m rtab t₀ y tr ar
  intro p
  have digits (z : Fin M→Cell s) : (encode s M z).val=∑i,(z i).val*(2^s)^i.val:=finFunctionFinEquiv_apply z
  have value : (data (fun h g=>kept f (t₀ h g) (x h g) (y h g)) p).val=
      (data (fun h g=>oldPart f (t₀ h g) (x h g)) p).val+(data (fun h g=>aliasPart f (t₀ h g) (y h g)) p).val :=by
    simp only [data,digits,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl;intro i _
    by_cases alive:p.2.val*M+i.val<G
    · simp only [dite_eq_left alive,pieces,Nat.add_mul]
    · simp [alive]
  simp only [header,Expr.eval,RowOp.opcode,BinaryOp.eval,l p,r p,value,Nat.cast_add]

/-- All operations on the receiving rectangle share these 28 static pages. -/
def tablesIndex : (Field×(Fin 2×Fin 2))≃Fin (7*(2*2)) :=
  ((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv

def pages (s t M : ℕ) (idx : Fin (7*(2*2))) : ROM.Page :=
  let z:=tablesIndex.symm idx
  if z.2.1.val=0 then ROM.binary (oldPart (s:=s) z.1) M z.2.2 else ROM.binary (aliasPart (s:=s) (t:=t) z.1) M z.2.2

def bits (s t M : ℕ):=max ((s+s)*M) ((s+t)*M)
def chart (base s t M : ℕ) (f : Field) (role : Fin 2) :=
  ROM.joined (pages s t M) (bits s t M) base (fun j=>tablesIndex (f,role,j))

theorem page_room (s t M : ℕ) (i : Fin (7*(2*2))) : (pages s t M i).bits≤bits s t M :=by
  obtain ⟨⟨f,r,j⟩,rfl⟩:=tablesIndex.surjective i
  have hs := Nat.mul_le_mul_right M (Nat.le_max_left s t)
  have ht := Nat.mul_le_mul_right M (Nat.le_max_right s t)
  fin_cases r <;> fin_cases j <;> simp [pages,ROM.binary,bits,Equiv.symm_apply_apply,Nat.add_mul] <;> omega

theorem installed (base s t M : ℕ) (f : Field) (m : Memory w) :
    let state:=ROM.after (pages s t M) (bits s t M) base m
    Static (chart base s t M f 0) (oldPart (s:=s) f) M state ∧
    Static (chart base s t M f 1) (aliasPart (s:=s) (t:=t) f) M state :=by
  intro state
  constructor <;> apply ROM.binary_mounted _ _ _ _ _ _ (page_room s t M) _ <;> intro j <;> simp [pages]

end
end Hierarchy.DescentResetRetainedPages

end OAI
