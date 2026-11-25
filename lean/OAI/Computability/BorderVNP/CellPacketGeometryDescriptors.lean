import OAI.Computability.BorderVNP.CellPacketGeometryDirectory
import OAI.Computability.BorderVNP.CellPacketGeometryMarkers
import OAI.Computability.BorderVNP.CellPacketSources

/-! # Three addressed fields for each sparse cell chunk

Public chunks use the returned positions of the first and last words of their
own section. Original boxes use the independently computed site delivery pointer.
Filtering these descriptors by cell gives the exact native chunk table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry

open Packing.Word RoutingISA.CellPacket CellSparse CellSparse.Packet.Source

/-- Source-word references of a public block, or the upstream absolute received-slot
operand of an original box. Neither alternative contains private factor bytes. -/
inductive Reference (N : ℕ) (E : Type*) where
  | words (first last : Fin N)
  | site (slot : E)
  | blank

variable {C N p d k w : ℕ} {E S : Type*}

-- Only the finite source ordinal is used in the public chunk expressions.
/-- A reference generates exactly three output words for the native dispatcher. -/
def Reference.fields (fit : C+N+C ≤ 2^p) (dest H : ℕ) :
    Reference N E → Fin 3 → WidthExpr (E ⊕ Fin (2^p))
  | .words first last => publicDescriptor dest (Markers.dataRow fit first) (Markers.dataRow fit last)
  | .site slot => privateDescriptor slot H
  | .blank => fun _ => .const 0

/-- Concrete three words read by a cell, obtained by evaluating the public
expressions. -/
def Reference.values (fit : C+N+C ≤ 2^p) (dest H : ℕ) (oper : E ⊕ Fin (2^p) → ℕ)
    (ref : Reference N E) : List ℕ := List.ofFn fun j => ((ref.fields fit dest H) j).eval oper

private theorem values_words (fit : C+N+C ≤ 2^p) (dest H : ℕ)
    (oper : E ⊕ Fin (2^p) → ℕ) (a b : Fin N) :
    (Reference.words a b).values fit dest H oper =
      [0,dest+oper (.inr (Markers.dataRow fit a)),
       oper (.inr (Markers.dataRow fit b))-oper (.inr (Markers.dataRow fit a))+1] := by
  simp [Reference.values,List.ofFn_succ,Reference.fields,publicDescriptor,addressExpr,extentExpr,
    WidthExpr.eval,Op.apply]

private theorem values_site (fit : C+N+C ≤ 2^p) (dest H : ℕ)
    (oper : E ⊕ Fin (2^p) → ℕ) (slot : E) :
    (Reference.site slot).values fit dest H oper = [1,oper (.inl slot),H] := by
  simp [Reference.values,List.ofFn_succ,Reference.fields,privateDescriptor,WidthExpr.eval]

/-- An unused reserved descriptor is a triple of zeros before the local tally scan. -/
theorem Reference.values_blank (fit : C+N+C ≤ 2^p) (dest H : ℕ) (oper : E ⊕ Fin (2^p) → ℕ) :
    (Reference.blank : Reference N E).values fit dest H oper = [0,0,0] := by
  simp [Reference.values,List.ofFn_succ,Reference.fields,WidthExpr.eval]

/-- Word-size checks for every descriptor field and each of its intermediates.
The same check works before selecting any private values or actual permutation. -/
theorem Reference.fits (fit : C+N+C ≤ 2^p) (dest H : ℕ) (up : Columns p d k w E → Bool)
    (π : Equiv.Perm (Fin (2^p))) (ref : Reference N E) (i : Fin 3)
    (endFit : dest+2^p < 2^w) (headerFit : H < 2^w) (one : 1 < 2^w) :
    (ref.fields fit dest H i).Fits w (operands up π) := by
  have hw : w ≠ 0 := by rintro rfl; simp at one
  cases ref with
  | words a b =>
    have ha := (π.symm (Markers.dataRow fit a)).isLt
    have hb := (π.symm (Markers.dataRow fit b)).isLt
    fin_cases i <;> simp [Reference.fields,publicDescriptor,addressExpr,extentExpr,
      WidthExpr.Fits,WidthExpr.eval,Op.apply,operands,hw] <;> omega
  | site s =>
    have hs := ParseBatchSort.value_lt (fun j : Fin w => up (.inr (.inr (.inl (s,j)))))
    fin_cases i <;> simp [Reference.fields,privateDescriptor,WidthExpr.Fits,operands,hw,hs,headerFit]
  | blank => exact Nat.two_pow_pos _

/-- Source references certify the first/last *raw* word at each public prefix.
The site clause checks an individual geometry slot operand. The private body
remains wholly absent from the reference and from all its address arithmetic. -/
inductive Links {Site : Type} (owner : Fin N → Fin C) (c : Fin C) (arg : E → ℕ)
    (slot : Site → ℕ) : ℕ → List (CellSparse.Packet.Source.Part Site) → List (Reference N E) → Prop
  | nil (pos) : Links owner c arg slot pos [] []
  | words {pos : ℕ} {xs : List ℕ} {ps : List (CellSparse.Packet.Source.Part Site)} {refs : List (Reference N E)}
      (a b : Fin N) (nonempty : 0 < xs.length)
      (firstOwner : owner a = c) (lastOwner : owner b = c)
      (first : (((List.finRange N).take a.val).filter fun t => decide (owner t = c)).length = pos)
      (last : (((List.finRange N).take b.val).filter fun t => decide (owner t = c)).length = pos+xs.length-1)
      (rest : Links owner c arg slot (pos+xs.length) ps refs) :
      Links owner c arg slot pos (.publicWords xs :: ps) (.words a b :: refs)
  | site {pos : ℕ} {ps : List (CellSparse.Packet.Source.Part Site)} {refs : List (Reference N E)} (j : Site) (s : E)
      (pointer : arg s = slot j) (rest : Links owner c arg slot pos ps refs) :
      Links owner c arg slot pos (.original j :: ps) (.site s :: refs)

/-- All addresses and lengths in the three-word array coincide with the native
typed source plan, including the variable cell-wide record tail. -/
theorem Links.descriptors {Site : Type} {owner : Fin N → Fin C} {c : Fin C} {arg : E → ℕ}
    {slot : Site → ℕ} {pos : ℕ} {ps : List (CellSparse.Packet.Source.Part Site)} {refs : List (Reference N E)}
    (h : Links owner c arg slot pos ps refs) (fit : C+N+C ≤ 2^p) (dest H : ℕ)
    (fs : Site → List Factor) (π : Equiv.Perm (Fin (2^p)))
    (sorted : Monotone fun i => 2*Markers.key owner (Markers.row C N (π i).val)*2^p+(π i).val) :
    refs.flatMap (Reference.values fit dest H (Sum.elim arg (fun i => (π.symm i).val))) =
      RoutingISA.CellPacket.descriptors
        (chunks slot H fs (dest+(π.symm (Markers.start fit c)).val+1+pos) ps) := by
  induction h with
  | nil => rfl
  | @words pos xs ps refs a b nonempty firstOwner lastOwner first last rest ih =>
    have ha := (Markers.rank_prefix fit owner c π sorted a firstOwner).trans (congrArg (_ + ·) first)
    have hb := (Markers.rank_prefix fit owner c π sorted b lastOwner).trans (congrArg (_ + ·) last)
    simp only [List.flatMap_cons,values_words,Sum.elim_inr,chunks,RoutingISA.CellPacket.descriptors,
      List.cons_append,List.nil_append,Chunk.descriptor,ha,hb] at ih ⊢
    rw [ih]
    have length_eq (r : ℕ) : r+1+(pos+xs.length-1)-(r+1+pos)+1 = xs.length := by omega
    rw [length_eq]
    simp only [Nat.add_assoc]
  | site j s pointer rest ih =>
    simp only [List.flatMap_cons,values_site,Sum.elim_inl,pointer,chunks,
      RoutingISA.CellPacket.descriptors,List.cons_append,List.nil_append,Chunk.descriptor] at ih ⊢
    rw [ih]

/-- Global sparse descriptor source rows. Triples are adjacent in raw order and
receive the common runtime owner of their part. -/
def descriptorRows (parts : List (Fin C × Reference N E)) (fit : C+N+C ≤ 2^p) (dest H : ℕ) :
    List (Fin C × WidthExpr (E ⊕ Fin (2^p))) :=
  parts.flatMap fun z => (List.ofFn (z.2.fields fit dest H)).map (fun e => (z.1,e))

/-- The padded sort reserves exactly three live input words per source part. -/
theorem descriptorRows_length (parts : List (Fin C × Reference N E)) (fit : C+N+C ≤ 2^p) (dest H : ℕ) :
    (descriptorRows parts fit dest H).length = 3*parts.length := by
  induction parts with
  | nil => rfl
  | cons hd tl ih => simp [descriptorRows] at ih ⊢; omega

/-- Stable selection keeps all three words of each part and no field from other
cells, even if several parts reference the same static payload. -/
theorem select_descriptors (parts : List (Fin C × Reference N E)) (fit : C+N+C ≤ 2^p) (dest H : ℕ)
    (oper : E ⊕ Fin (2^p) → ℕ) (c : Fin C) :
    ((descriptorRows parts fit dest H).filter (fun v => decide (v.1 = c))).map
      (fun v => v.2.eval oper) =
      ((parts.filter (fun v => decide (v.1 = c))).map Prod.snd).flatMap (Reference.values fit dest H oper) := by
  induction parts with
  | nil => rfl
  | cons z ps ih =>
    by_cases eqn : z.1 = c <;>
      simp [descriptorRows,List.ofFn_succ,Reference.values,eqn] at ih ⊢ <;> exact ih

end CellPacketGeometry

end BorderVNP
end Computability
end OAI
