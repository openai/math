import OAI.Hierarchy.DescentStageCablePorts
import OAI.Hierarchy.DescentPackedCensusRAM
import OAI.Hierarchy.DescentPackedCensusRows
import OAI.Hierarchy.DescentIssuedReset

namespace OAI
/-! # Fixed-capacity SIMD census at a genuine selected group stage -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentSIMDLookup DescentColonies StarKeys PackedCensus
open Computability.VPVNP.BurstRAM PrivateRAM DescentCompiler
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
  {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (S : AtomSchedule)
local notation "Q" => (A.z*G.b)
variable {H R b cap : ℕ} (name : V ↪ Fin H) (group : J ≃ Fin R) (slots : A.PortOrder cap)

private def hole : Cell ((1+b+2*cap)*2^k) :=
  encode _ _ (fun _=>header b cap ((0,0),fun _=>0))

def rawCensus (b : ℕ) (v : Fin H) (g : Fin R) : Cell ((1+b+2*cap)*2^k) :=
  if live : ∃u,name u=v then
    source W A.pos A.block A.grainCount A.quantum_positive (fun t=>A.hub t.2) A.records b cap slots (group.symm g,live.choose)
  else hole

def censusValue (marked : Bool) (v : Fin H) (g : Fin R) (x : Block k) : ℕ :=
  if live : ∃u,name u=v then
    if marked then blockMass W.graph A.pos A.block (fun u=>(W.core.filter (fun e=>W.graph.src e=u)).card)
      (group.symm g,live.choose) x
    else blockMass W.graph A.pos A.block (W.siteUnits (fun u=>A.hub (A.pos u).2) A.records A.wire 256 A.hist)
      (group.symm g,live.choose) x
  else 0

theorem stage_lookup (ready : A.StateBounds S i) (marked : Bool) (v : Fin H) (g : Fin R) :
    PackedCensus.lookup marked b cap k A.wire 256 Q A.hist (A.rawCensus name group slots b v g)=
      encode b (2^k) (fun x=>((A.censusValue name group marked v g x:ℕ):Cell b)) := by
  by_cases h : ∃u,name u=v
  · simp only [rawCensus,censusValue,dite_eq_left h]
    exact source_read W A.pos A.block A.grainCount A.quantum_positive (fun t=>A.hub t.2)
      A.records b cap slots marked A.wire 256 Q A.hist (A.grainCount_fit S ready) _
  · simp only [rawCensus,censusValue,dite_eq_right h,hole,PackedCensus.lookup,Equiv.symm_apply_apply]
    apply congrArg (encode b (2^k))
    funext x
    cases marked <;> simp [Function.comp_apply,evaluate,numPaid,numLive]

theorem census_le (ready : A.StateBounds S i) (flag : Bool) (v : Fin H) (g : Fin R) (x : Block k) :
    A.censusValue name group flag v g x≤A.wire*Q*A.cap := by
  by_cases h : ∃u,name u=v
  · simp only [censusValue,dite_eq_left h]
    cases flag
    · exact A.small _ _
    · rw [ite_eq_left rfl,←out_eq]
      let toPort:=portOfOut W A.pos A.block A.grainCount A.quantum_positive (group.symm g,h.choose) x
      have bound:= (Fintype.card_le_of_injective toPort toPort.injective).trans
        (A.local_port_count S ready (group.symm g) h.choose x)
      have coef : 1≤A.wire*Q:=Nat.mul_pos A.wirePos (Nat.mul_pos A.unitPos G.base_pos)
      exact bound.trans (by simpa only [one_mul] using Nat.mul_le_mul_right A.cap coef)
  · simp [censusValue,h]

theorem census_nat (ready : A.StateBounds S i) (precision : A.wire*Q*A.cap<2^b)
    (flag : Bool) (v : Fin H) (g : Fin R) (x : Block k) :
    ((A.censusValue name group flag v g x:ℕ):Cell b).val=A.censusValue name group flag v g x :=
  Fin.val_cast_of_lt ((A.census_le S name group ready flag v g x).trans_lt precision)

theorem packed_census_frames {M w : ℕ} (ready : A.StateBounds S i) (first second : DescentSIMDLookup.Banks)
    (lo hi : ℕ)
    (fit1 : Fits first ((1+b+2*cap)*2^k) (b*2^k) M H R w lo)
    (fit2 : Fits second ((1+b+2*cap)*2^k) (b*2^k) M H R w lo)
    (fit3 : Fits second ((1+b+2*cap)*2^k) (b*2^k) M H R w hi)
    (gap : lo+H*chunks R M≤hi) (m : Memory w)
    (loaded : ∀marked : Bool,PinFrame (M:=M) (if marked then second else first)
      (PackedCensus.lookup marked b cap k A.wire 256 Q A.hist) (A.rawCensus name group slots b) m) :
    ∃out,(histograms first second lo hi H R M w).Exec m out (clocks first second H R M) ∧
    (∀marked : Bool,∀p : Row H R M,out ((if marked then hi else lo)+(row H R M p).val)=
      ((data (fun v g=>encode b (2^k) (fun x=>((A.censusValue name group marked v g x:ℕ):Cell b))) p).val:Word w)) ∧
    (∀a<lo,out a=m a) ∧ ∀a,hi+H*chunks R M≤a→ out a=m a := by
  obtain ⟨out,run,h₁,h₂,keep,after⟩:=histograms_frames first second lo hi fit1 fit2 fit3 gap
    (PackedCensus.lookup false b cap k A.wire 256 Q A.hist)
    (PackedCensus.lookup true b cap k A.wire 256 Q A.hist) _ m (loaded false) (loaded true)
  refine ⟨out,run,?_,keep,after⟩
  intro marked p
  cases marked
  · simpa only [Bool.false_eq_true,↓reduceIte,A.stage_lookup S name group slots ready] using h₁ p
  · simpa only [↓reduceIte,A.stage_lookup S name group slots ready] using h₂ p

theorem packed_census {M w : ℕ} (ready : A.StateBounds S i) (first second : DescentSIMDLookup.Banks)
    (lo hi : ℕ)
    (fit1 : Fits first ((1+b+2*cap)*2^k) (b*2^k) M H R w lo)
    (fit2 : Fits second ((1+b+2*cap)*2^k) (b*2^k) M H R w lo)
    (fit3 : Fits second ((1+b+2*cap)*2^k) (b*2^k) M H R w hi)
    (gap : lo+H*chunks R M≤hi) (m : Memory w)
    (loaded : ∀marked : Bool,PinFrame (M:=M) (if marked then second else first)
      (PackedCensus.lookup marked b cap k A.wire 256 Q A.hist) (A.rawCensus name group slots b) m) :
    ∃out,(histograms first second lo hi H R M w).Exec m out (clocks first second H R M) ∧
    (∀marked : Bool,∀p : Row H R M,out ((if marked then hi else lo)+(row H R M p).val)=
      ((data (fun v g=>encode b (2^k) (fun x=>((A.censusValue name group marked v g x:ℕ):Cell b))) p).val:Word w)) ∧
    ∀a<lo,out a=m a := by
  obtain ⟨out,run,read,low,_⟩:=A.packed_census_frames S name group slots ready first second lo hi fit1 fit2 fit3 gap m loaded
  exact ⟨out,run,read,low⟩

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
