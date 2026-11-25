import OAI.Hierarchy.TaggedWireHistorySockets
import OAI.Hierarchy.TaggedWireInstalledRows
import OAI.Hierarchy.ProtocolRAMCatalogueCoreMount
import OAI.Hierarchy.TaggedWideActivePartition

namespace OAI
/-! # Positive reported chords in either native row orientation -/
noncomputable section
open scoped Fin.CommRing
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open AdaptiveProbe ProbeStage CoreBoard ReportSockets WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical
variable {h W k attempts M : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marked : Marks h W k attempts) (unique : Exclusive marked)
    (b : Board) (order : Fin b.coreRows≃Edges S h (2^W) k) (acquired : Bought S π depth marked→Fin b.boughtRows)
    (raw : Fin b.rows→ProtocolRAMEmit.Row)
local notation "ordinal" => b.original S π depth marked order acquired
local notation "name" => siteNumber h (2^W) k
local notation "K" => siteLast h (2^W) k+1
variable (receipt : Alignment b S π depth marked M raw (fun i=>(raw i).width)
    (b.original S π depth marked order acquired))
variable (B : Mount (S:=S) π (siteNumber h (2^W) k) b.rows) (pad : Chord (siteLast h (2^W) k+1))


theorem edgeOfRow (i : {i : Fin b.rows // 0<(raw i).width})
    (printed :
      ((B.actual.tail i.val).val=(raw i.val).endpoint ∧ (B.actual.head i.val).val=(raw i.val).opposite) ∨
      ((B.actual.tail i.val).val=(raw i.val).opposite ∧ (B.actual.head i.val).val=(raw i.val).endpoint)) :
    filledChord B.actual pad i.val=HistoryRoles.sorted S π depth marked (.inl (receipt.ident i)) := by
  let z:=actualEnds S π depth marked (receipt.ident i)
  have distinct : name z.1≠name z.2:=(name).injective.ne (actual_distinct S π depth marked (receipt.ident i))
  have pair : (B.actual.tail i.val=name z.1 ∧ B.actual.head i.val=name z.2) ∨
      (B.actual.tail i.val=name z.2 ∧ B.actual.head i.val=name z.1) := by
    rcases printed with ⟨t,h⟩|⟨t,h⟩ <;> rcases receipt.joins i with ⟨e,o⟩|⟨e,o⟩
    · exact Or.inl ⟨Fin.ext (t.trans e),Fin.ext (h.trans o)⟩
    · exact Or.inr ⟨Fin.ext (t.trans e),Fin.ext (h.trans o)⟩
    · exact Or.inr ⟨Fin.ext (t.trans o),Fin.ext (h.trans e)⟩
    · exact Or.inl ⟨Fin.ext (t.trans o),Fin.ext (h.trans e)⟩
  change filledChord B.actual pad i.val=orderedChord (name z.1) (name z.2) distinct
  rcases pair with ⟨one,two⟩|⟨one,two⟩
  · simp [filledChord,one,two,distinct]
  · by_cases lt:name z.1<name z.2
    · simp [filledChord,one,two,distinct.symm,orderedChord,lt,not_lt.mpr lt.le]
    · have gt:name z.2<name z.1:=lt_of_le_of_ne (le_of_not_gt lt) distinct.symm
      simp [filledChord,one,two,distinct.symm,orderedChord,lt,gt]

theorem mounted_chord {w : ℕ} (m : Memory w)
    (read : ∀j : Fin b.boughtRows,Reads (raw (b.boughtIndex j)) (b.bought.view m (j.val:Word w))
      (b.idBase+(b.boughtIndex j).val))
    (i : {i : Fin b.rows // 0<(raw i).width}) :
    filledChord (b.coreMount π name order m).actual pad i.val=
      HistoryRoles.sorted S π depth marked (.inl (receipt.ident i)) := by
  apply edgeOfRow S π depth marked b order acquired raw receipt _ pad i
  obtain ⟨l,r⟩|⟨l,r⟩:=receipt.coreMount_sites m read i ((receipt.geometry 1 1).fits i)
  · exact Or.inl ⟨congrArg Fin.val l,congrArg Fin.val r⟩
  · exact Or.inr ⟨congrArg Fin.val l,congrArg Fin.val r⟩

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment
end

end OAI
