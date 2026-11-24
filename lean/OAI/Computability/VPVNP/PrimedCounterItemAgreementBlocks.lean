import OAI.Computability.VPVNP.PrimedCounterItemAgreementCore
import OAI.Computability.VPVNP.PrimedCounterKernel
import OAI.Computability.VPVNP.PrimedStackRAMVisit
import OAI.Computability.VPVNP.PrimedStackRAMFootprint

/-!
# Agreement of the four parser routines

An administrative routine consumes an empty tape. A node consumes the binary
words selected by its current pending degree. In both cases the post-memory
of the routine represents the indicated logical state, and the dispatcher's
ticks preserve that memory for the next call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.ItemAgreement

open BurstRAM PrimedStackRAM PrimedInputRAM
open scoped Fin.CommRing

variable {L : Lengths} {n r H s w : ℕ} {Q : Layout L n r H w} {D : Data Q s}
variable {st : VisitState n n s} {shared : Internal L r H w → Bool} {bits : List Bool}
variable {mem : Memory w} {native : Option (Report w)} {next : Option (Word w)}
variable {regs : Regs w 16} {state : Word w}

theorem clear (hf : D.Fits) (held : D.Holds shared st mem) (j : Fin n) (hj : regs 2 = (j.val : Word w))
    (fr : Framed native next 15 D.fuel D.parserPub state Admin.clear regs mem bits) :
    ItemAgreement D shared mem next (if bits = [] then some {st with marked := st.marked.erase j} else none) native := by
  split
  · rename_i hb
    obtain ⟨es,rs,he,hp,hl,hbits,ha⟩ := Admin.clear_cell D.parserPub_stack hf.scratch state regs mem j hj
    apply accept_of_framed fr he _ (hbits.trans hb.symm) hf (Admin.clear_holds held.1 j hf.scratch) held.2 ha
    · rw [hp]; decide
    · rw [hl]; unfold Data.fuel; omega
  · exact reject_nonempty fr ‹bits ≠ []›

theorem init (hf : D.Fits) (held : D.Holds shared st mem)
    (fr : Framed native next 15 D.fuel D.parserPub state Admin.init regs mem bits) :
    ItemAgreement D shared mem next (if bits = [] then some {st with pending := [(D.degree,D.root)]} else none) native := by
  split
  · rename_i hb
    obtain ⟨es,rs,he,hp,hl,hbits,_,_,ha⟩ := Admin.init_cell D.parserPub_stack hf.scratch state regs mem
      D.degree D.root D.parserPub_root.1 D.parserPub_root.2.1
    apply accept_of_framed fr he _ (hbits.trans hb.symm) hf (Admin.root_holds held.1 D.degree D.root hf.scratch) held.2 ha
    · rw [hp]; decide
    · rw [hl]; unfold Data.fuel; omega
  · exact reject_nonempty fr ‹bits ≠ []›

theorem compare (hf : D.Fits) (held : D.Holds shared st mem) (j : Fin D.labels) (hj : regs 7 = (j.val : Word w))
    (fr : Framed native next 9 D.fuel D.parserPub state Admin.compare regs mem bits) :
    ItemAgreement D shared mem next
      (if bits = [] ∧ st.counts ((labelIndex n n s).symm j) = D.nomination ((labelIndex n n s).symm j)
       then some st else none) native := by
  have hpre := hf.headers.trans (Nat.le_add_right Q.scratchBase (PrimedInputRAM.positions n r))
  obtain ⟨hyes,hno⟩ := Admin.compare_cell D.parserPub_stack hf.scratch state regs mem held.1 j hj L
    D.parserPub_root.2.2 hpre
  rw [held.2 j, D.nominated_value hf j] at hyes hno
  split
  · rename_i hh
    obtain ⟨es,rs,he,hp,hl,hbits⟩ := hyes hh.2
    apply accept_of_framed fr he _ (hbits.trans hh.1.symm) hf held.1 held.2 (fun _ _ => rfl)
    · rw [hp]; decide
    · rw [hl]; unfold Data.fuel; omega
  · rename_i hh
    by_cases hb : bits = []
    · apply reject_of_framed fr
      intro es rs m' hx
      exact (hno (fun h => hh ⟨hb,h⟩) es rs m' hx).elim
    · exact reject_nonempty fr hb

theorem node (hf : D.Fits) (held : D.Holds shared st mem) (g : Fin 2) (v : Fin (2^r))
    (hrow : regs 5 = (↑((g.val*2^r+v.val)*n) : Word w))
    (hmass : leafMass st.pending ≤ n) (hcounts : ∀ a, st.counts a+1 < 2^w)
    (fr : Framed native next 16 D.fuel (D.parserPub ∘ Admin.stackPublic) state nodeFlow regs mem bits) :
    ItemAgreement D shared mem next (visit w (D.input shared g v) st bits) native := by
  rw [D.parserPub_stack] at fr
  let pub := publicData w D.base (2^r) n n s
  have ha := completeNode_visit held.1 g v state regs bits hrow hf.scratch hf.states hf.word
    (by simpa [pow_two] using hf.triangle) hmass hcounts
  cases hr : completeNode pub state regs mem bits with
  | none =>
    change Agreement D.base (D.input shared) _ (completeNode pub state regs mem bits) at ha
    rw [hr] at ha
    cases hv : visit w (D.input shared g v) st bits <;> rw [hv] at ha <;> cases ha
    apply reject_of_framed fr
    intro es rs m' hx hb
    have ht := (completeNode_iff_exec (o := ⟨es,rs,m',[]⟩)).mpr ⟨hx,hb.symm,rfl⟩
    rw [hr] at ht
    contradiction
  | some o =>
    change Agreement D.base (D.input shared) _ (completeNode pub state regs mem bits) at ha
    rw [hr] at ha
    cases hv : visit w (D.input shared g v) st bits <;> rw [hv] at ha <;> cases ha
    obtain ⟨hx,hbits,_⟩ := completeNode_iff_exec.mp hr
    have hl := node_refines.bounded (Option.filter_eq_some_iff.mp hr).1
    exact accept_of_framed fr hx (by unfold Data.fuel; omega) hbits.symm hf (by assumption) held.2
      (completeNode_below hf.scratch hr) (by assumption)

end PrimedCounter.ItemAgreement

end VPVNP
end Computability
end OAI
