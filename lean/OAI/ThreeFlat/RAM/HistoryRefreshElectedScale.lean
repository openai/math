import OAI.ThreeFlat.RAM.HistoryRefreshBatchRates

namespace OAI
/-! # Width of the elected refresh batch -/
set_option quotPrecheck false

namespace ThreeFlat.RAM.HistoryRefreshEmitter

set_option maxRecDepth 6000

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree HistoryPartyBatchExec
open HistoryBoundedJoin HistoryMotifJoin HistoryPartyBatch HistoryBoundedBody BitNetwork.Ordered
open scoped BigOperators Classical Fin.CommRing

noncomputable section
variable {W p a b : ℕ} {F : Type*}
variable [CommRing F]

section Elected
open Diagonal Diagonal.MotifOrderedCells Diagonal.MotifOuterTerms Diagonal.MotifSelectorChecks
open HistoryPartySpecialization HistoryPartyTapeRun
variable {K : Type} [CommRing K] [Fintype K] {H : Type*} {r s e k b d B ar : ℕ}
  (tile : Tile K H e d b) (good : (Fin (e*k)→Bool)→Prop) (letter : (Fin (e*k)→Bool)→Fin s)
  (tp : b+(e*d+e*d)≤ar) (sp : e*k+s≤ar)
  (A : HistoryPartyBatch.Layout) (input : Memory W) (t : Fin (B+1))

def electedBatch (checks : Bool) : HistoryPartyBatchExec.Build W :=
  ⟨A,checks,HistoryPartySpecialization.kind tile good letter tp sp,input⟩

def tag (g : (Fin 3→Bool)→K) : ℕ := (Fintype.equivFin _ g).val
local notation "SC" => MotifNativeCompactors.partialInput K r t.val
local notation "PC" => MotifNativeCompactors.partialInput K (r*d) t.val
local notation "lib" => HistoryStaticArchive.all K ar

private theorem elected_boot_scale (A : HistoryPartyBatch.Layout) (ck : Bool) (input : Memory W)
    (r d t : ℕ) (room : A.seed+37<2^W)
    (away : ∀ x, HistoryPartyBootExec.SeedRead A ck (numeric input) x → x<A.seed ∨ A.seed+37≤x)
    (power : 2^Nat.clog 2 (HistoryPartyBootExec.extent A (numeric input))<2^W)
    (copies : numeric (HistoryPartyBootExec.output A ck input)
      ((HistoryPartyBatch.registers A ck (numeric input)).incident+3)=r)
    (digit : numeric (HistoryPartyBootExec.output A ck input)
      ((HistoryPartyBatch.registers A ck (numeric input)).grid+4)=d)
    (exponent : numeric (HistoryPartyBootExec.output A ck input)
      ((HistoryPartyBatch.registers A ck (numeric input)).dyadic+1)=t) :
    Nat.clog 2 (HistoryPartyBootExec.extent A (numeric input))=t ∧
      t=HistogramTileNetwork.siteHeight r d ∧ t≤W := by
  let m := numeric input
  let regs := HistoryPartyBatch.registers A ck m
  let image := HistoryPartyBootExec.output A ck input
  have kept (address : ℕ) (probe : HistoryPartyBootExec.SeedRead A ck m address) :
      numeric image address=m address :=
    congrArg Fin.val (HistoryPartyBootExec.output_outside A ck input room address (away address probe))
  change numeric image (regs.incident+3)=r at copies
  change numeric image (regs.grid+4)=d at digit
  have extent : HistoryPartyBootExec.extent A m=max r (r*d) := by
    by_cases active : occupied A m
    · have inc : regs.incident=incident A m := ite_eq_left active
      have grid : regs.grid=shape A m := ite_eq_left active
      have count : m (incident A m+3)=r := by
        rw [←kept _ (.copyCount active), ←inc]
        exact copies
      have width : m (shape A m+4)=d := by
        rw [←kept _ (.digitWidth active), ←grid]
        exact digit
      simp only [HistoryPartyBootExec.extent, HistoryPartyBatch.copies, HistoryPartyBatch.digit,
        ite_eq_left active, count, width]
    · have inc : regs.incident=A.seed+15 := ite_eq_right active
      rw [inc] at copies
      change (HistoryPartyBootExec.output A ck input (A.seed+18)).val=r at copies
      have zero : HistoryPartyBootExec.seedMemory A ck input (A.seed+18)=0 :=
        HistoryPartyBootExec.seedMemory_at A ck input (18 : Fin 37)
      rw [HistoryPartyBootExec.output_at A ck input room (A.seed+18),
        ite_eq_right (by omega : A.seed+18≠A.seed+3), ite_eq_right (by omega : A.seed+18≠A.seed+2), zero] at copies
      have absent : 0=r := copies
      simp [HistoryPartyBootExec.extent, HistoryPartyBatch.copies, active, ←absent]
  let level := Nat.clog 2 (HistoryPartyBootExec.extent A m)
  have width : level<W := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp power
  change (HistoryPartyBootExec.output A ck input (A.seed+2)).val=t at exponent
  rw [HistoryPartyBootExec.output_at A ck input room (A.seed+2),
    ite_eq_right (by omega : A.seed+2≠A.seed+3), ite_eq_left rfl] at exponent
  change ((level : Word W)).val=t at exponent
  rw [Fin.val_cast_of_lt (width.trans Nat.lt_two_pow_self)] at exponent
  refine ⟨exponent, exponent.symm.trans ?_, exponent ▸ width.le⟩
  change Nat.clog 2 (HistoryPartyBootExec.extent A m)=Nat.clog 2 (max r (r*d))
  rw [extent]

private theorem header_digit (headerKind : HistoryPartyHeader.Kind) :
    headerKind.words (4 : Fin 7) = headerKind.digit := rfl

private theorem observed_scale {n : ℕ} (A : HistoryPartyBatch.Layout) (ck : Bool)
    (input : Memory W) (headerKind : HistoryPartyHeader.Kind) (catalog : HistoryStaticArchive.Catalog K n ar)
    (r d : ℕ) (t : Fin (B + 1)) (jobs : List (HistoryReadyTape.Job W)) (width : headerKind.digit = d) :
    let X : HistoryPartyBatchExec.Build W := ⟨A, ck, headerKind, input⟩
    Reads X.regs (numeric X.bootImage) catalog r t → X.Source jobs →
      Nat.clog 2 (HistoryPartyBootExec.extent A (numeric input)) = t.val ∧
        t.val = HistogramTileNetwork.siteHeight r d ∧ t.val ≤ W := by
  intro X read source
  have digit : numeric X.bootImage (X.regs.grid + 4) = d :=
    (source.gridRead 4).trans ((header_digit headerKind).trans width)
  exact elected_boot_scale A ck input r d t.val source.seedRoom source.seedAway source.power
    read.copies digit read.exponent

private theorem elected_kind_digit :
    (HistoryPartySpecialization.kind tile good letter tp sp).digit = d := rfl

private theorem elected_scale (ck : Bool) (jobs : List (HistoryReadyTape.Job W)) :
    let X := electedBatch tile good letter tp sp A input ck
    Reads X.regs (numeric X.bootImage) lib r t → X.Source jobs →
    Nat.clog 2 (HistoryPartyBootExec.extent A (numeric input))=t.val ∧
      t.val=HistogramTileNetwork.siteHeight r d ∧ t.val≤W :=
  observed_scale A ck input (HistoryPartySpecialization.kind tile good letter tp sp) (HistoryStaticArchive.all K ar)
    r d t jobs (elected_kind_digit tile good letter tp sp)


end Elected

end
end ThreeFlat.RAM.HistoryRefreshEmitter

end OAI
