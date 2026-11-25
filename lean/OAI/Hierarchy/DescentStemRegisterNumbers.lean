import OAI.Hierarchy.DescentStemCoordinateObserved
import OAI.Hierarchy.DescentStemNumberOperands
import OAI.Hierarchy.DescentResetStemNumberRead

namespace OAI
/-! # The physical six-register book authenticated against the original installed stem numbers -/
noncomputable section
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase DescentChosenRouter
open DescentResetCompactParent DescentResetCableSlots DescentResetOrdinalDigits DescentResetWireTags
open DescentRouterSlots DescentPackedTicketChronology DescentOrderedReset
open DescentResetSourceTicketRAM DescentResetSourceTicketCompare
open DescentSIMDLookup DescentGL DescentResetStemCompactOrder DescentIssuedFallbackPanel
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "ng" => S.groupCount (i+1)
local notation "X" => 2^k
local notation "J" => stemsCount B
local notation "K" => totalLocal B
local notation "count₀" => 2^(S.groupWidth k tail i+k-B.terminals.commonDepth)
variable {N field b M Wd : ℕ}
open DescentResetFieldAssembler DescentResetStemProjectIndex DescentResetStemGroupPlane
variable (receivers : Fin N→Option B.next.V)

open DescentStemNumberOperands DescentResetStemFlagInputs
open DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure

def numberPlan (N M field signedBits selfBits metaBits : ℕ) : Plan :=
  ⟨coords B N M field,signedBits,selfBits,metaBits⟩

def originalRegisters {signed self «meta» : ℕ} (base : ℕ) (saved : Bank)
    (chip : Fin X→Fin J→Expr) (bias : Expr) (header : Fin X→Fin J→Expr) (x : Fin X) (j : Fin J) : Fin 6→Expr :=
  (numberPlan B N M field signed self «meta»).stem base saved x (stemTag B j).2.1 (chip x j) bias (header x j)

theorem registers_issued {signed self «meta» : ℕ} (base : ℕ) (saved : Bank) (mem : Memory Wd)
    (chip : Fin X→Fin J→Expr) (bias : Expr) (header : Fin X→Fin J→Expr)
    (vchip : Fin X→Fin J→Fin N→Fin ng→Cell signed) (vself : Fin N→Cell self)
    (chosen : mem saved.base=((DescentExterior.matrixCode B.frame.basis).val:Word Wd)) (savedEarly : saved.Fits Wd base)
    (room : (numberPlan B N M field signed self «meta»).endAddress base<2^Wd)
    (cs : ∀x j,(chip x j).Fits Wd base) (bs : bias.Fits Wd base) (hs : ∀x j,(header x j).Fits Wd base)
    (chips : ∀x j,Source (chip x j) (vchip x j) M mem) (biases : Source bias (fun v (_:Fin ng)=>vself v) M mem)
    (headers : ∀x j,Source (header x j) (fun v g₀=>DescentResetFieldAssembler.raw «meta» (actualMeta B receivers x (stemShelf B j) v g₀)) M mem)
    (metaPos : 0<«meta») :
    let P:=numberPlan B N M field signed self «meta»
    let term:=originalRegisters (N:=N) (M:=M) (field:=field) (signed:=signed) (self:=self) («meta»:=«meta») B base saved chip bias header
    let dst:=P.image base mem
    (∀x j t,(term x j t).Fits Wd (P.endAddress base)) ∧
    (∀x j,Source (term x j 0) (fun v g₀=>((vchip x j v g₀).val:Cell field)) M dst) ∧
    (∀x j,Source (term x j 1) (fun (_:Fin N) g₀=>(stemGroupDigit B x (stemTag B j).2.1 g₀:Cell field)) M dst) ∧
    (∀x j,Source (term x j 2) (fun v (_:Fin ng)=>((vself v).val:Cell field)) M dst) ∧
    (∀x j,Source (term x j 3) (fun (_:Fin N) g₀=>(stemFineDigit B x (stemTag B j).2.1 g₀:Cell field)) M dst) ∧
    (∀x j,Source (term x j 4) (fun v g₀=>((actualMeta B receivers x (stemShelf B j) v g₀).live.toNat:Cell field)) M dst) ∧
    (∀x j,Source (term x j 5) (fun (_:Fin N) (g₀ : Fin ng)=>firstDigit field x.val g₀) M dst) :=by
  intro P term dst
  have first (x : Fin X) (j : Fin J) :=P.read base mem room 0 (chip x j) (vchip x j) (cs x j) (chips x j)
  have second :=P.read base mem room 1 bias (fun v (_:Fin ng)=>vself v) bs biases
  have third (x : Fin X) (j : Fin J) :=P.read base mem room 2 (header x j)
    (fun v g₀=>DescentResetFieldAssembler.raw «meta» (actualMeta B receivers x (stemShelf B j) v g₀)) (hs x j) (headers x j)
  have addr (x : Fin X) (j : Fin J) (t : Fin 3) :=P.coordinates base saved mem B.frame.basis chosen savedEarly room t x (stemTag B j).2.1
  have casted (d : Meta) : P.convert 2 (DescentResetFieldAssembler.raw «meta» d)=(d.live.toNat:Cell field):=by
    have view:=digit_encode (fun i=>(digits d i:Cell «meta»)) (0:Fin 7)
    have bit : d.live.toNat<2^«meta»:= (Nat.lt_of_le_of_lt (Bool.toNat_le _) (Nat.one_lt_two_pow (by omega)))
    change ((digit «meta» 0 ((encode «meta» 7 _).val):ℕ):Cell field)=_
    exact congrArg (fun n : ℕ => (n : Cell field)) (view.trans (Fin.val_cast_of_lt (n:=2^«meta») bit))
  have relabel {e : Expr} {source target : Fin N→Fin ng→Cell field}
      (read : Source e source M dst) (same : ∀v g₀,source v g₀=target v g₀) : Source e target M dst := by
    exact (funext (fun v => funext (same v))) ▸ read
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro x j t
    fin_cases t
    · exact (first x j).1
    · exact (addr x j 0).1
    · exact second.1
    · exact (addr x j 1).1
    · exact (third x j).1
    · exact (addr x j 2).1
  · intro x j
    exact relabel (first x j).2 (fun _ _ => rfl)
  · intro x j
    exact relabel (addr x j 0).2 (fun _ g₀ => congrArg (fun n : ℕ => (n : Cell field))
      (coords_group B N M field g₀ x (stemTag B j).2.1))
  · intro x j
    exact relabel second.2 (fun _ _ => rfl)
  · intro x j
    exact relabel (addr x j 1).2 (fun _ g₀ => congrArg (fun n : ℕ => (n : Cell field))
      (coords_fine B N M field g₀ x (stemTag B j).2.1))
  · intro x j
    exact relabel (third x j).2 (fun v g₀ => casted (actualMeta B receivers x (stemShelf B j) v g₀))
  · intro x j
    exact relabel (addr x j 2).2 (fun _ g₀ => (congrArg (fun n : ℕ => (n : Cell field))
      (coords_zero B N M field g₀ x (stemTag B j).2.1)).trans (stem_public_zero (field:=field) x g₀))

end Hierarchy.DescentSixParty.ClosedReset.Window

end
end OAI
