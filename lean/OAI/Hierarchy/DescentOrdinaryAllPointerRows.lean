import OAI.Hierarchy.DescentOrdinaryIssuedPointers
import OAI.Hierarchy.DescentPointerDigitHeader

namespace OAI
/-! # Every ordinary output header is a pointer, including rows outside the live trace -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedPriorOperand DescentOperandStateBanks DescentPriorOperandColumns DescentPackedOperand
open DescentOrdinaryFinal DescentOrdinaryAtomFieldRAM DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentLocalPrivateNames Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F Q : Type} [Field F] (v : PhysicalOrdinary F Q)
local notation "L" => v.resolver
local notation "B" => v.finalChart
variable («meta» : v.MetaWords) (old : Books (L)) (jobs : Fin (L).jobs→DescentDatedPriorOperand.Source (L))
local notation "cells" => v.numericInputs «meta» old jobs

def writtenOperandBooks : Books (L) :=fun x p h g=>(B).law p ((B).dataAt cells p x h g)

theorem written_pointers : BookPointers (v.writtenOperandBooks «meta» old jobs) :=by
  apply (books_typed_iff _).2
  intro x n arg h g
  let pg:=pageOf arg
  let inp:=fun (f : Fin 4)=>(B).dataAt cells (pg f) x h g
  let seat:=(B).slots (n,arg)
  have keys (f : Fin 4) (s : Fin (B).keys) : (B).stamp (inp f) s=(B).stamp (inp 0) s:=
    (v.issued_stamp «meta» old jobs x h g (pg f) s).trans (v.issued_stamp «meta» old jobs x h g (pg 0) s).symm
  have ar (f : Fin 4) (u : Fin (L).nodes) : (B).arity (inp f) u=(B).arity (inp 0) u:=
    (v.issued_arity «meta» old jobs x h g (pg f) u).trans (v.issued_arity «meta» old jobs x h g (pg 0) u).symm
  have live (f : Fin 4) (s : Fin (B).keys) : (B).live (inp f) s ↔ (B).live (inp 0) s:=by
    unfold Chart.live
    dsimp only
    rw [ar f ((B).slots.symm s).1]
  have same (f : Fin 4) : (B).marked (inp f)=(B).marked (inp 0):=by
    funext s
    simp only [Chart.marked,live f,keys f]
  have result (f : Fin 4) : ScalarOperand.take n (v.writtenOperandBooks «meta» old jobs x (pg f) h g)=
      (B).lane (pg f) (inp f) n:=congrFun ((encode _ _).symm_apply_apply _) n
  have id_ (f : Fin 4) : (B).pages.symm (pg f)=(f.castLE (by decide : 4≤7),arg):=
    (finProdFinEquiv : Fin 7×Fin (L).operands ≃ _).symm_apply_apply _
  have good (f : Fin 4) : f.val<4:=f.isLt
  by_cases used : (B).live (inp 0) seat
  · let code:=(B).stamp (inp 0) seat
    let d:=digit ((L).size+4)
    let name:=renameDigit ((B).marked (inp 0)) seat
    have width : 2<2^(B).field:=(by decide : 2<2^2).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_left 2 (L).size))
    obtain ⟨p,hp⟩:=component_typed (B).field width (d 0 code) (d 2 code) (d 3 code) (d 4 code) name
    refine ⟨p,fun f=>?_⟩
    change (ScalarOperand.take n (v.writtenOperandBooks «meta» old jobs x (pg f) h g)).val = _
    rw [result f]
    simp only [Chart.lane,id_ f,Fin.val_castLE,dite_eq_left (good f)]
    change (if (B).live (inp f) seat then _ else (0 : Cell (B).field)).val = _
    rw [ite_eq_left ((live f seat).mpr used),keys f seat,same f]
    exact hp f
  · obtain ⟨p,hp⟩:=typed_zero (width:=(B).field)
    refine ⟨p,fun f=>?_⟩
    change (ScalarOperand.take n (v.writtenOperandBooks «meta» old jobs x (pg f) h g)).val = _
    rw [result f]
    simp only [Chart.lane,id_ f,Fin.val_castLE,dite_eq_left (good f)]
    change (if (B).live (inp f) seat then _ else (0 : Cell (B).field)).val = _
    rw [ite_eq_right (fun h => used ((live f seat).mp h))]
    exact hp f

theorem written_pointer_rows {w} (floor : ℕ) (safe : (B).Early (v.finalSources floor) (v.metaEnd floor) w)
    (room : v.afterEnd floor<2^w) (m : Memory w)
    (newRead : ∀f x,Reads (v.nodeChart.bank (v.nodeBankBase floor) f x) («meta» f x) (L).lanes m)
    (spanRead : ∀x p,Reads (previousBank (L) (v.vectorOutput floor) x p) (old x p) (L).lanes m)
    (keyRead : ∀j,Reads (Banks.wordBank (L) (v.normalizedEnd floor) j)
      (fun h g=>word ((jobs j).compiled h g)) (L).lanes m) :
    BookPointers (v.writtenOperandBooks «meta» old jobs) ∧ ∀x pg,
      Reads (previousBank (L) ((B).out (v.metaEnd floor)) x pg) (v.writtenOperandBooks «meta» old jobs x pg)
        (L).lanes ((v.argumentsAfter floor safe room).image m) :=
  ⟨v.written_pointers «meta» old jobs,
    v.argumentsAfter_issued floor safe room m «meta» old jobs newRead spanRead keyRead⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
