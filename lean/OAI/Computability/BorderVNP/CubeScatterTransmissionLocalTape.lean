import OAI.Computability.BorderVNP.CubeScatterTransmissionAssigned

/-! # Reconstructing the entire actual local transmission tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter
open private index_covered from OAI.Computability.BorderVNP.TransmissionSharedLastWrite
open private receivedWord_at from OAI.Computability.BorderVNP.CubeScatterTransmissionAssigned

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins}
variable {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ} {a q blocks K h : ℕ}
variable {decl : LengthDeclaration a q} {group : Fin q → Fin (R+1)} {anchor : Fin (R+1)}

private theorem sharedHere_fields {r : Range w} {self : Word w} (mode : r.selected self = some (some .sharedHere)) :
    r.kind = 0 ∧ self = r.teamA ∧ r.teamA = r.teamB := by
  by_cases tag : r.kind = 0 <;> by_cases data : r.kind = 1 <;>
    by_cases left : self = r.teamA <;> by_cases same : r.teamA = r.teamB <;> by_cases right : self = r.teamB <;>
    simp_all [Range.selected,Range.bank,decision,Decision.role]

/-- All actual local transmission choices are exactly the co-owned slots of
the returned row words. Neither a remote bit nor any literal or substituted
data bit can insert an additional chronological guess. -/
theorem SharedWriters.recovered_local_tape (writer : SharedWriters f g src)
    (frame : SymbolFrame g (src anchor) blocks K h decl group) (dataCount : (D.directory pp lp).length = g.dataCount)
    (u : Fin (R+1)) :
    (H u).history.val.1.flatMap TeamRAM.Event.choices =
      tableChoiceBits (H u).rows (H u).team (assignedShared g (f.receivedRows g group)) (H u).count := by
  have round : tableChoiceBits (H u).rows (H u).team (H u).bits (H u).count = List.ofFn (H u).word.val :=
    tableChoiceBits_decodeChoices (H u).rows (H u).team (List.ofFn (H u).word.val) (by simp)
  apply ((H u).stream.trans round.symm).trans
  apply (tableChoiceBits_eq_iff_slot_eq ..).mpr
  intro i hi mode j hj
  obtain ⟨tag,self,same⟩ := sharedHere_fields mode
  have shared : g.dataCount ≤ i := by
    by_contra! data
    have one := (f.placed u).columns.kind ⟨i,dataCount.symm ▸ data⟩
    have eq := congrArg Fin.val (one.symm.trans tag)
    simp only [Fin.val_one',Fin.val_zero,Nat.mod_eq_of_lt (Nat.one_lt_pow f.word.ne' (by decide : 1<2))] at eq
    omega
  have reach : i < f.table.count := (f.fullCount u) ▸ hi
  obtain ⟨y,hy,x,hxy,index⟩ := index_covered g shared (writer.count ▸ reach)
  let sym : Symbols q := ⟨(⟨x,frame.groups ▸ hxy.trans hy⟩,⟨y,frame.groups ▸ hy⟩),hxy⟩
  obtain ⟨_,ha,hb,width,_⟩ := tableRange_fields (f.image u) f.allocated (f.records u) reach
  rw [← f.ranges u] at ha hb width
  have first : (f.row i).first = u.val := ha.symm.trans ((congrArg Fin.val self).symm.trans (f.bank u).team)
  have second : (f.row i).second = u.val := hb.symm.trans ((congrArg Fin.val same).symm.trans (ha.trans first))
  have inside : j < (f.row i).width := hj.trans_eq width
  have idx : i = sharedIndex g sym := index
  rw [idx] at first second inside ⊢
  have digit := writer.local_digit u hxy hy first second inside
  have ueq : group sym.val.1 = u := Fin.ext ((writer.declaredRows frame sym).1.symm.trans first)
  have len : j < (f.receivedRows g group sym).length := by
    simpa only [ReturnedDelivery.receivedRows,receivedWord_length,sharedIndex] using inside
  rw [assignedShared_at _ _ _ _ len]
  have read := receivedWord_at (H (group sym.val.1)).history.val.2.2 (g.view x y) (f.row (sharedIndex g sym)).width j len
  exact digit.symm.trans ((congrArg (fun t => decide (((H t).history.val.2.2 (g.view x y+j)).val=1)) ueq.symm).trans read.symm)

end TeamContraction

end BorderVNP
end Computability
end OAI
