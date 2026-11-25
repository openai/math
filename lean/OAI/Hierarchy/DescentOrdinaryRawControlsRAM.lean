import OAI.Hierarchy.DescentOrdinaryRawTests

namespace OAI
/-! # Literal native readers of both endpoint flags and the parent multiplicity -/
namespace Hierarchy.DescentOrdinarySignedMeta.RawControls
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local
open DescentOrdinaryAtomFieldRAM.ROM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open private DescentPacking.PackedMatch.Local.Gather.zero_fields from OAI.Hierarchy.DescentPackedFieldGather
open scoped Classical Fin.CommRing
noncomputable section

def width (a M : ℕ) := (a*11+1)*M

def pages (a b M : ℕ) : Fin (2+2)→Page :=
  Fin.addCases (binary (rawFlags (a:=a)) M) (binary (rawUnits (a:=a) (b:=b)) M)

def stop (base a M : ℕ) := base+4*2^width a M

def flagsTable (base a b M : ℕ) := joined (pages a b M) (width a M) base (Fin.castAdd 2)
def unitsTable (base a b M : ℕ) := joined (pages a b M) (width a M) base (Fin.natAdd 2)

theorem bitsBound (a b M : ℕ) (i : Fin (2+2)) : (pages a b M i).bits ≤ width a M := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [pages,Fin.addCases_left]
    fin_cases j <;> change _*M ≤ _*M <;> apply Nat.mul_le_mul_right <;> omega
  · intro j
    simp only [pages,Fin.addCases_right]
    fin_cases j <;> change _*M ≤ _*M <;> apply Nat.mul_le_mul_right <;> omega

theorem issued {H G M a b w : ℕ} (base : ℕ) (tab : Fin 11→Tables) (f : Fin 11→Expr) (bit : Expr)
    (m : Memory w) (room : stop base a M<2^w)
    (gatherBounds : Gather.Bounds (d:=a) (M:=M) (w:=w) tab f base)
    (gatherStatic : ∀i,Static (tab i) (Gather.setField (d:=a) i) M m)
    (bitFit : bit.Fits w base)
    (words : Fin H→Fin G→Fin 11→Cell a) (core : Fin H→Fin G→Cell 1)
    (old : ∀i,Source (f i) (fun h g=>words h g i) M m) (marked : Source bit core M m) :
    let p:=pages a b M
    let dst:=after p (width a M) base m
    let rowExpr:=Gather.assembly tab f
    let value:=fun h g=>encode a 11 (words h g)
    let flags:=(flagsTable base a b M).read rowExpr bit
    let units:=(unitsTable base a b M).read rowExpr bit
    (mount p (width a M) w base).Exec m dst (4+10*(4*2^width a M)) ∧
    flags.Fits w (stop base a M) ∧ units.Fits w (stop base a M) ∧
    Source flags (fun h g=>rawFlags (value h g) (core h g)) M dst ∧
    Source units (fun h g=>rawUnits (b:=b) (value h g) (core h g)) M dst := by
  intro p dst rowExpr value flags units
  have fitR : rowExpr.Fits w base := Gather.fits tab f base gatherBounds (List.finRange 11)
  have raw : Source rowExpr value M m := by
    simpa [rowExpr,value,Gather.assembly] using Gather.collected tab f base gatherBounds m gatherStatic words old (List.finRange 11)
  have lo : base ≤ stop base a M := Nat.le_add_right ..
  have held {c : ℕ} (e : Expr) (v : Fin H→Fin G→Cell c) (fit : e.Fits w base) (got : Source e v M m) :
      Source e v M dst := fun i=>(ProtocolRAM.eval_below e _ m dst fit (fun t ht=>
        DescentOrdinaryAtomFieldRAM.ROM.frame p (width a M) base m t (.inl ht))).trans (got i)
  have bf (i : Fin (2+2)) : (bank p (width a M) base i).Fits w (stop base a M) :=
    bank_room p (width a M) base _ i (bitsBound a b M i) le_rfl room
  have guardF : Fits (flagsTable base a b M) rowExpr bit (a*11) 1 M (stop base a M) w :=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ lo fitR,ProtocolRAMGeneratedWrite.fits_mono _ lo bitFit,bf _,bf _,
      by rfl,by rfl⟩
  have guardU : Fits (unitsTable base a b M) rowExpr bit (a*11) 1 M (stop base a M) w :=
    ⟨guardF.left,guardF.right,bf _,bf _,by rfl,
      by rfl⟩
  have emptyF : rawFlags (a:=a) 0 0=0 := by
    simp [rawFlags,activeRaw,DescentPacking.PackedMatch.Local.Gather.zero_fields]
  have emptyU : rawUnits (a:=a) (b:=b) 0 0=0 := by
    simp [rawUnits,activeRaw,DescentPacking.PackedMatch.Local.Gather.zero_fields]
  refine ⟨(DescentStaticWordColumn.mount base _ _ m room),?_,?_,?_,?_⟩
  · simp [flags,Tables.read,Expr.Fits,guardF.left,guardF.right,guardF.shift,guardF.apply]
  · simp [units,Tables.read,Expr.Fits,guardU.left,guardU.right,guardU.shift,guardU.apply]
  · exact read_data _ rowExpr bit _ guardF _ emptyF dst
      (binary_mounted _ M p (width a M) base m (bitsBound a b M) (Fin.castAdd 2) (fun j=>by fin_cases j <;> rfl))
      value core (held rowExpr value fitR raw) (held bit core bitFit marked)
  · exact read_data _ rowExpr bit _ guardU _ emptyU dst
      (binary_mounted _ M p (width a M) base m (bitsBound a b M) (Fin.natAdd 2) (fun j=>by fin_cases j <;> rfl))
      value core (held rowExpr value fitR raw) (held bit core bitFit marked)

end
end Hierarchy.DescentOrdinarySignedMeta.RawControls

end OAI
