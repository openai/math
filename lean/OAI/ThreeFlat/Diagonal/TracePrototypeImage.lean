import OAI.ThreeFlat.Diagonal.TraceBitAddresses
import OAI.ThreeFlat.Diagonal.TraceWorkspaceSectors
import OAI.ThreeFlat.Diagonal.TraceSeedImage
import OAI.ThreeFlat.RAM.TracePrototypeBoot

namespace OAI
/-! # Selected native H startup at its actual three finite banks -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM RAM RAM.PhysicalProcedure RAM.EffectStream TraceStaticRow
open LaneCursor LaneCursor.RowLayout
open scoped Fin.CommRing
variable {F : Type} [Field F] [Fintype F] {u S fuel q low : ℕ}
local notation "wordWidth" => 16*u^10
local notation "dH" => ((q+1)+low)
variable (hF : Fintype.card F ≤ 2^(16*u^10)) (hw : 3 ≤ 16*u^10+1) (hp : u ≤ 2^(16*u^10+1))
  (base : ℕ) (st : Word (16*u^10)) (hs : S ≤ 2^(16*u^10)) (hf : fuel ≤ 2^(16*u^10+1))
  (grid : S+fuel ≤ 2^(1+((q+1)+low)))
local notation "G" => gateTable hF hw hp base fuel st u u dH
local notation "K" => TraceBitDescriptor.records (p:=u) (r:=u) (k:=u) (d:=dH) hw base S fuel
local notation "P" => layout hF hw hp base st hs hf u u grid
local notation "b" => TickWorkspace.base u
local notation "es" => bankRecords (W:=wordWidth) hF hw hp base st hs hf u u grid (b 54) (b 55) (b 56)
local notation "shared" => TraceUniformRow.SharedCount wordWidth u u u dH fuel
variable (codec : FieldCode F (16*u^10)) (parameterBase directoryWords : ℕ)
local notation "boot" => TracePrototypeBoot.cursor u parameterBase directoryWords S shared (List.length es) G codec

theorem prototype_budget (large : bitParameterConstant≤u) (hq : Fintype.card F≤u)
    (upper : dH≤15*u^10) : (boot).budget≤2*u^152 := by
  let n := (G).cells+2*(1+(dH+dH))
  have el : (es).length=n := by
    simp only [bankRecords,seedRecords_length,n,two_mul]
  have age : 20000≤u := (by decide : 20000≤bitParameterConstant).trans large
  have cost : 10^26*17^14≤u := (by decide : 10^26*17^14≤bitParameterConstant).trans large
  have seed := seed_volume (f:=fuel) age cost hq upper hF hw hp base st
  change 2*n*wordWidth+(2*n*(5*wordWidth+6)+6+(4+6*n))≤u^152 at seed
  have value := diagonal_bitParameterLength_le_pow (by omega) hq upper hF hw hp base fuel st large
  let c := FixedTraceImage.count G
  change wordWidth*c≤u^151 at value
  have up : 0<u := by omega
  have wpos : 0 < wordWidth := by positivity
  have charge : c*(5*wordWidth+6)≤11*u^151 := by
    calc c*(5*wordWidth+6) ≤ c*(11*wordWidth) := Nat.mul_le_mul_left _ (by omega)
         _ = 11*(wordWidth*c) := by ring
         _ ≤ 11*u^151 := Nat.mul_le_mul_left _ value
  have growth : 12000*u^151≤u^152 := by
    rw [pow_succ u 151,Nat.mul_comm (u^151) u]
    exact Nat.mul_le_mul_right _ (by omega)
  have pos : 0<u^151 := pow_pos up _
  change c*(5*wordWidth+6)+6+(2*(es).length*(5*wordWidth+6)+6+(4+6*(es).length))+(4+18*(2*(3*18+1)+4))≤_
  rw [el]
  omega

/-- The finite packed table survives the sparse scatter and the S57 header install.
The same result contains the actual compiler coefficient IDs, XOR masks, reverse
dictionary and the eighteen public operands of the scalar reader. -/
theorem prototype_image (m : Memory wordWidth) (localTable : FixedTraceImage.count G≤TickWorkspace.stride u)
    (offsets : 1+(dH+dH)≤TickWorkspace.stride u) (rows : 2^dH≤TickWorkspace.stride u)
    (wordSpace : b 56+TickWorkspace.stride u≤2^wordWidth)
    (lib : Fintype.card ((Fin 3→Bool)→F)≤2^wordWidth) :
    let out := (boot).image u G codec K es m
    let table := FixedTraceImage.packed G codec K (b 53) m
    (∀ a,b 53≤a → a<b 53+FixedTraceImage.count G → out a=table a) ∧
    Banks hF hw hp base st hs hf u u grid (b 54) (b 55) (b 56) out ∧
    (∀ i : Fin FixedTraceProgram.P, out (b 57+i.val)=(boot).reader i) := by
  intro out table
  have h53 := TickWorkspace.apart (u:=u) (by decide : 53<54)
  have h54 := TickWorkspace.apart (u:=u) (by decide : 54<55)
  have h55 := TickWorkspace.apart (u:=u) (by decide : 55<56)
  have h56 := TickWorkspace.apart (u:=u) (by decide : 56<57)
  have h57 := TickWorkspace.apart (u:=u) (by decide : 57<58)
  have drows : 2^(q+1)*2^low≤TickWorkspace.stride u := by simpa only [pow_add] using rows
  have count : (G).cells≤TickWorkspace.stride u := by unfold FixedTraceImage.count at localTable; omega
  have room : SeedRoom (G).cells (1+(dH+dH)) (2^(q+1)*2^low) (b 54) (b 55) (b 56) wordWidth :=
    ⟨by omega,by omega,by omega⟩
  let packed := fillSegment (b 58) (2*(es).length) (packedWord (b 58) es) table
  let scattered := after packed (events es)
  have below (z : ℕ) (h : z<b 57) : out z=scattered z :=
    TraceRawLookup.installed_outside (TracePrototypeBoot.readerLayout u) (boot).reader scattered (Or.inl h)
  have banks := seed_image hF hw hp base st hs hf u u grid (b 54) (b 55) (b 56) packed room lib
  refine ⟨?_,?_,?_⟩
  · intro z left right
    have earlier : z<b 54 := by omega
    have kept : scattered z = packed z := (P).seed_outside (b 54) (b 55) (b 56)
      (fun j : Fin (G).cells => ((HistoryCompiledRows.library G).id j).val) packed room z (Or.inl earlier)
    exact (below z (by omega)).trans (kept.trans
      (ite_eq_right (by omega : ¬(b 58≤z ∧ z<b 58+2*(es).length))))
  · refine ⟨?_,?_,?_⟩
    · intro j
      rw [below (b 54+j.val) (by have := j.isLt; omega)]
      exact banks.1 j
    · intro a
      have offs := ((P).offset ((P).code a)).isLt
      rw [below (b 56+((P).offset ((P).code a)).val) (by omega)]
      exact banks.2.1 a
    · intro i
      have := i.isLt
      rw [below (b 55+i.val) (by omega)]
      exact banks.2.2 i
  · intro i
    exact congrFun (TraceRawLookup.installed_words (TracePrototypeBoot.readerLayout u) (boot).reader scattered) i


/-- Initializing the compact H reader leaves every earlier bank, including the
terminal edge-prefix journal and all S44 node pointers, at its input value. -/
theorem prototype_below (m : Memory wordWidth) (localTable : FixedTraceImage.count G≤TickWorkspace.stride u)
    (offsets : 1+(dH+dH)≤TickWorkspace.stride u) (rows : 2^dH≤TickWorkspace.stride u)
    (wordSpace : b 56+TickWorkspace.stride u≤2^wordWidth) (z : ℕ) (hz : z<b 53) :
    (boot).image u G codec K es m z=m z := by
  have h53:=TickWorkspace.apart (u:=u) (by decide : 53<54)
  have h54:=TickWorkspace.apart (u:=u) (by decide : 54<55)
  have h55:=TickWorkspace.apart (u:=u) (by decide : 55<56)
  have h56:=TickWorkspace.apart (u:=u) (by decide : 56<57)
  have h57:=TickWorkspace.apart (u:=u) (by decide : 57<58)
  have drows : 2^(q+1)*2^low≤TickWorkspace.stride u := by simpa only [pow_add] using rows
  have count : (G).cells≤TickWorkspace.stride u := by unfold FixedTraceImage.count at localTable;omega
  have room : SeedRoom (G).cells (1+(dH+dH)) (2^(q+1)*2^low) (b 54) (b 55) (b 56) wordWidth :=
    ⟨by omega,by omega,by omega⟩
  let table:=FixedTraceImage.packed G codec K (b 53) m
  let staged:=fillSegment (b 58) (2*(es).length) (packedWord (b 58) es) table
  have outsideHeader : (boot).image u G codec K es m z = after staged (events es) z :=
    TraceRawLookup.installed_outside (TracePrototypeBoot.readerLayout u) (boot).reader _
      (Or.inl (show z<b 57 by omega))
  have outsideBanks : after staged (events es) z = staged z := (P).seed_outside (b 54) (b 55) (b 56)
    (fun j : Fin (G).cells => ((HistoryCompiledRows.library G).id j).val) staged room z (Or.inl (by omega))
  have outsideScratch : staged z = table z :=
    ite_eq_right (by omega : ¬(b 58≤z ∧ z<b 58+2*(es).length))
  have outsideTable : table z = m z :=
    ite_eq_right (by omega : ¬(b 53≤z ∧ z<b 53+FixedTraceImage.count G))
  exact outsideHeader.trans (outsideBanks.trans (outsideScratch.trans outsideTable))


end ThreeFlat.Diagonal.TraceBitHeader

end OAI
