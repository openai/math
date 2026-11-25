import OAI.Hierarchy.TaggedWideDatedOrientation
import OAI.Hierarchy.TaggedWideDatedRoleSheets

namespace OAI
/-! # A single observed original inventory determines all three native date columns -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows
open WireTelescope AdaptiveProbe ReportSockets ProtocolRAM Calendar CatalogueRows RoleProgram
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
variable {h W k attempts N native : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (mark : ReportSockets.Marks h W k attempts) (unique : Exclusive mark)
    (b : CatalogueRows.Board) (order : Fin b.coreRows≃Edges S h (2^W) k)
    (size : attempts*(ProtocolRAM.PurchaseFrozen.count h (2^W) k*ProtocolRAM.PurchaseFrozen.paths h S.degree depth)=b.boughtRows)
    (rows : Fin N≃Source S π depth mark)
local notation "I" => Old h W k b.rows
local notation "K" => Fintype.card I
local notation "e" => b.ordinal S π depth mark order size
local notation "src" => lookup S π depth mark b order size rows
local notation "idx" => raw S π depth mark b order size rows
local notation "ids" => embed S π depth mark b order size
local notation "side" => inputSide S π depth mark rows
local notation "siteCount" => siteLast h (2^W) k+1
local notation "D" => stride k S.degree attempts

/-- The dated assembly only reads actual physical original row expressions. The
thin chronological row family and the normalized two endpoint orientations follow
from the public source injection and its partial inverse. -/
theorem sheet_reads (L : Chart) (sock : Bool→Socket) (table : Bank) (amount number : Expr)
    (m : Memory native) (qty id : I→ℕ) (pay : Fin b.rows→Bool→Public S h W k attempts)
    (widthRead : ∀j : Fin K,(amount.eval m (j.val:Word native)).val=qty (SettledMatrix.Layout.numbered j))
    (idRead : ∀j : Fin K,(number.eval m (j.val:Word native)).val=id (SettledMatrix.Layout.numbered j))
    (vac : ∀i : Fin b.rows,i∉Set.range e→qty (.inl i)=0)
    (opened : ∀a : Catalogue S π depth mark,0<qty (.inl (e a))→∀t,pay (e a) t=
      .inl (HistoryRoles.paid S π depth mark unique (a,t)))
    (original : ∀j : Fin K,0<qty (SettledMatrix.Layout.numbered j)→∀t,
      Resolved S L (sock t) m (j.val:Word native) (publicRoleFor S π pay (SettledMatrix.Layout.numbered j) t))
    (room : siteCount≤2^native) (strides : ∀s : Fin siteCount,table.read m (s.val:Word native)=((s.val*D:ℕ):Word native)) :
    DatedRoleSheets.Reads K L sock table amount number S π depth mark unique rows m (qty∘ids∘rows)
      (id∘ids∘rows) src side := by
  have numbered := numbered_raw S π depth mark b order size rows
  have rwQty (j : Fin K) := widthRead j
  have rwID (j : Fin K) := idRead j
  refine ⟨fun i _=>⟨idx i,lookup_live ..⟩,input_onto S π depth mark rows,
    input_flip S π depth mark rows,?_,?_,by omega,?_,?_,?_,fun p=>strides _⟩
  · intro i
    rw [Function.comp_apply,Function.comp_apply,←numbered i,←rwQty]
    exact Fin.isLt _
  · intro i
    rw [Function.comp_apply,Function.comp_apply,←numbered i,←rwID]
    exact Fin.isLt _
  · intro j
    apply Fin.ext
    have bound : qty (SettledMatrix.Layout.numbered j)<2^native := rwQty j ▸ Fin.isLt _
    cases found:src j with
    | none=>
      obtain ⟨r,same,empty⟩:=lookup_dormant S π depth mark b order size rows found
      rw [rwQty,same,vac r empty];rfl
    | some i=>
      obtain rfl:= (lookup_found S π depth mark b order size rows found).symm
      simp only [Option.elim_some,Function.comp_apply,rwQty,numbered,Fin.val_cast_of_lt (numbered i ▸ bound)]
  · intro j i found _
    have := lookup_found S π depth mark b order size rows found
    subst j
    have small : id (ids (rows i))<2^native:=by rw [←numbered,←rwID];exact Fin.isLt _
    apply Fin.ext
    simp only [Function.comp_apply,rwID,numbered,Fin.val_cast_of_lt small]
  · intro j i found pos bSide
    have := lookup_found S π depth mark b order size rows found
    subst j
    change 0<qty (ids (rows i)) at pos
    have resolved:=original (idx i) (by rwa [numbered]) bSide
    rw [numbered] at resolved
    have chosen (c) (hit:rows i=.inl c) := opened c (by simpa only [hit,embed,Function.Embedding.coe_sumMap,Sum.map_inl] using pos)
    have same : publicRoleFor S π pay (ids (rows i)) bSide =
        named S π depth mark unique rows (i,side i bSide) :=
      original_name S π depth mark unique rows e pay i bSide chosen
    rw [←same]
    exact resolved

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows

end
end OAI
