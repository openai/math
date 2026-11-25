import OAI.Hierarchy.DescentTrunkBitRefs
import OAI.Hierarchy.DescentBitHistoryCombine

namespace OAI
/-! # The old tensors, trunk equalities and physical router histories through a reset -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentResetAttachments DescentNamedContact DescentRouterBank
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {X Y : Type} {d n : ℕ} {P H Q : Type} [Fintype H] [Fintype Q] {bits : P→ℕ}
variable (N : Network n P bits) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group N.width))
variable {L : ℕ} (key : N.Edge↪Fin L)
local notation "M" => DescentResetTrunks.network N home group R
variable (old : SiteBits (U:=X) N) (bank : SiteBits (U:=Y) R)
def oldGather (h : H) (i : Fibre home h) : BitRecipe X (Boundary (M) (.inl (false,h))) (boundaryWidth (M) (.inl (false,h))) :=
  i.property ▸ (old i.val).reroute (trunkOldBit N home group R key i.val)

omit [Fintype Q] in
private theorem oldGather_read (scalar : X→List (List Bool)→F) (a : (M).Assignment) (pins : Ports bits) (h : H) (i : Fibre home h) :
    (oldGather N home group R key old h i).value scalar (bitInput (M) a pins (.inl (false,h)))=
     (old i.val).value scalar (bitInput N (oldRows N (DescentResetTrunks.Ordered.original N home group R key a) i.val) pins i.val) := by
  rcases i with ⟨v,rfl⟩
  rw [oldGather,BitRecipe.reroute_eval]
  apply congrArg ((old v).value scalar)
  funext e
  exact trunkOldBit_read N home group R key a pins v e

def oldProduct (h : H) := BitRecipe.combineBits (oldGather N home group R key old h) (Empty.elim : Empty→ℕ)
  (fun _=>Sum.inl)

omit [Fintype Q] in
theorem oldProduct_read (s : X→List (List Bool)→F) (tbl : N.Tables F) (valid : ReadsBits N s old tbl)
    (a : (M).Assignment) (pins : Ports bits) (h : H) :
    (oldProduct N home group R key old h).value s (bitInput (M) a pins (.inl (false,h)))=
      ∏v : Fibre home h,N.read tbl (oldRows N (DescentResetTrunks.Ordered.original N home group R key a) v.val) pins v.val := by
  rw [oldProduct,BitRecipe.combine_bits_value]
  simp only [Sum.elim_inl,Fintype.sum_unique]
  apply Finset.prod_congr rfl
  intro v _
  rw [oldGather_read,valid]

def equalWord (ws : List (List Bool)) : F := if ws.getD 0 []=ws.getD 1 [] then 1 else 0
def relay (h : H) : BitRecipe Unit (Boundary (M) (.inl (true,h))) (boundaryWidth (M) (.inl (true,h))) where
  Hidden := Empty
  hiddenWidth := Empty.elim
  Node := Fibre (DescentResetTrunks.moved N home) h
  tag _ := ()
  arity _ := 2
  size e _ := N.width e.val
  arg e side j := .inl (if side.val=0 then
    ⟨.inl ⟨.inr (.inl h),Or.inr rfl⟩,DescentOrderedWords.address (DescentOrderedReset.fibreKey key (DescentResetTrunks.moved N home) h) (fun i : Fibre (DescentResetTrunks.moved N home) h=>N.width i.val) ⟨e,j⟩⟩
    else ⟨.inl ⟨.inl (true,e.val),Or.inl (congrArg (fun q=>Sum.inl (true,q)) e.property)⟩,j⟩)

omit [Fintype Q] in
theorem relay_value (a : (M).Assignment) (pins : Ports bits) (h : H) :
    (relay N home group R key h).value (fun _=>equalWord (F:=F)) (bitInput (M) a pins (.inl (true,h)))=
    if ∀e,DescentResetTrunks.moved N home e=h→(DescentResetTrunks.Ordered.decode N home group R key a).2.1 e=(DescentResetTrunks.Ordered.decode N home group R key a).1 true e then 1 else 0 := by
  let : Unique ((i : (relay N home group R key h).Hidden) →
      Word ((relay N home group R key h).hiddenWidth i)) := by
    change Unique ((i : Empty) → Word (Empty.elim i))
    infer_instance
  unfold BitRecipe.value
  rw [Fintype.sum_unique]
  trans ∏e : Fibre (DescentResetTrunks.moved N home) h,
    if (DescentResetTrunks.Ordered.decode N home group R key a).2.1 e.val=(DescentResetTrunks.Ordered.decode N home group R key a).1 true e.val then (1:F) else 0
  · apply Finset.prod_congr rfl
    rintro ⟨e,rfl⟩ _
    simp [equalWord,relay,bitInput,boundaryRead,wordList,DescentResetTrunks.Ordered.decode,
      DescentOrderedReset.words,DescentOrderedWords.decode];
      exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)
  · rw [Fintype.prod_boole]
    simp only [Subtype.forall]

def bankPullback (v : R.Site) := (bank v).reroute (trunkBankBit N home group R key v)

omit [Fintype Q] in
theorem bankPullback_read (s : Y→List (List Bool)→F) (tbl : R.Tables F) (valid : ReadsBits R s bank tbl)
    (a : (M).Assignment) (pins : Ports bits) (v : R.Site) :
    (bankPullback N home group R key bank v).value s (bitInput (M) a pins (.inr v))=
      R.read tbl (DescentResetTrunks.Ordered.decode N home group R key a).2.2
        (DescentResetTrunks.Ordered.public N group key (DescentResetTrunks.Ordered.decode N home group R key a).1) v := by
  rw [bankPullback,BitRecipe.reroute_eval,←valid]
  apply congrArg ((bank v).value s)
  funext b
  exact trunkBankBit_read N home group R key a pins v b

def trunkScalar (s : X→List (List Bool)→F) (r : Y→List (List Bool)→F) :
    (X⊕(Unit⊕Y))→List (List Bool)→F := Sum.elim s (Sum.elim (fun _=>equalWord) r)

def trunkBits : SiteBits (U:=X⊕(Unit⊕Y)) (M)
  | .inl (false,h)=>(oldProduct N home group R key old h).retag Sum.inl
  | .inl (true,h)=>(relay N home group R key h).retag (Sum.inr ∘ Sum.inl)
  | .inr v=>(bankPullback N home group R key bank v).retag (Sum.inr ∘ Sum.inr)

omit [Fintype Q] in
theorem trunk_reads (s : X→List (List Bool)→F) (r : Y→List (List Bool)→F)
    (tbl : N.Tables F) (router : R.Tables F) (ht : ReadsBits N s old tbl) (hr : ReadsBits R r bank router) :
    ReadsBits (M) (trunkScalar s r) (trunkBits N home group R key old bank)
      (DescentResetTrunks.Ordered.tables N home group R key tbl router) := by
  intro a p v
  rw [show (M).read (DescentResetTrunks.Ordered.tables N home group R key tbl router) a p v=
    DescentResetTrunks.Ordered.factor N home group R key tbl router a p v from
    DescentLocalTables.read _ _ (DescentResetTrunks.Ordered.local_factor N home group R key tbl router) a p v]
  rcases v with ⟨_|_,h⟩|v
  · exact oldProduct_read N home group R key old s tbl ht a p h
  · exact relay_value N home group R key a p h
  · exact bankPullback_read N home group R key bank r router hr a p v

end
end Hierarchy.DescentKernelHistory

end OAI
