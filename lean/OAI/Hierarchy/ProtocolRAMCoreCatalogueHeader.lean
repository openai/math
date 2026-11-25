import OAI.Hierarchy.ProbeCoreCode
import OAI.Hierarchy.ProbeSiteAddress
import OAI.Hierarchy.ProbeReportSockets
import OAI.Hierarchy.ProtocolRAMReportGroupROM
import OAI.Hierarchy.ProbeStagePublicGroups
import OAI.Hierarchy.ProtocolRAMSupergroupDirectory

namespace OAI
/-! # Public row format for native core-catalogue endpoints

Free rows carry the two fixed site ordinals. Paid rows carry pointers to the
live CT group, inlet, and outlet words, together with the public stage-remap
base and the two layer tags. The input permutation occurs only on the CT tape.
-/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreCatalogue

open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard
open ThreeFlat.RAM
open scoped Fin.CommRing Classical

variable {h W k R w : ℕ} {S : PurchaseSampler}

def canonical (S : PurchaseSampler) (h W k : ℕ) :
    Fin (Fintype.card (Edges S h (2^W) k)) ≃ Edges S h (2^W) k := (Fintype.equivFin _).symm

def sideTag (k attempts : ℕ) (l : AdaptiveProbe.ColumnLayer k) (side : Bool) : ℕ :=
  (Fintype.equivFin (Bool × ReportSockets.Role k attempts) (side,.inl l)).val

def recordWord (attempts groupStart M : ℕ) (edge : Edges S h (2^W) k) : Fin 10 → ℕ :=
  match edge with
  | .inl f =>
    let ends := freeEnds f
    ![0,(siteNumber h (2^W) k ends.1).val,(siteNumber h (2^W) k ends.2).val,
      0,0,0,0,0,0,coreCode S M (.inl f)]
  | .inr ((p,t),l) =>
    let ct := Native.stageBank h (2^W) (PurchaseCT.stageNumber t)
    ![1,0,0,(ct 0).base+p.val,(ct 1).base+p.val,(ct 2).base+p.val,
      (ReportGroupROM.bank groupStart h (2^W) t).base,sideTag k attempts l false,sideTag k attempts l true,1]

def stride (R : ℕ) := ProtocolRAMSupergroupDirectory.span R

def headerBank (base R : ℕ) (field : Fin 10) : Bank :=
  ⟨base+field.val*stride R,ProtocolRAMSupergroupDirectory.bits R⟩

def headerWords (R : ℕ) := 10*stride R

theorem headerWords_linear (R : ℕ) : headerWords R ≤ 20*(R+1) := by
  have h := ProtocolRAMSupergroupDirectory.space R
  unfold headerWords stride
  omega

/-- One format-only tape under an arbitrary prescribed catalogue ordinal. -/
def mountHeader (order : Fin R ≃ Edges S h (2^W) k) (base attempts groupStart M : ℕ)
    (m : Memory w) : Memory w :=
  fillSegment base (headerWords R) (fun a =>
    let x := a-base
    if cf : x/stride R < 10 then
      if cr : x%stride R < R then (recordWord attempts groupStart M (order ⟨_,cr⟩) ⟨_,cf⟩ : Word w)
      else 0
    else 0) m

def Header (order : Fin R ≃ Edges S h (2^W) k) (base attempts groupStart M : ℕ) (m : Memory w) : Prop :=
  ∀ (f : Fin 10) (r : Fin R), m ((headerBank base R f).base+r.val) =
    (recordWord attempts groupStart M (order r) f : Word w)

theorem header_cell (base R : ℕ) (f : Fin 10) (r : Fin R) :
    base ≤ (headerBank base R f).base+r.val ∧ (headerBank base R f).base+r.val < base+headerWords R := by
  have lim := Nat.mul_le_mul_right (stride R) f.isLt
  rw [Nat.succ_mul] at lim
  have small : r.val < stride R := r.isLt.trans (ProtocolRAMSupergroupDirectory.slotFits R)
  simp only [headerBank,headerWords]
  omega

theorem mountHeader_read (order : Fin R ≃ Edges S h (2^W) k) (base attempts groupStart M : ℕ)
    (m : Memory w) : Header order base attempts groupStart M (mountHeader order base attempts groupStart M m) := by
  intro f r
  have bound := header_cell base R f r
  simp only [headerBank,Nat.add_assoc] at bound
  have small : r.val < stride R := r.isLt.trans (ProtocolRAMSupergroupDirectory.slotFits R)
  have pos : 0 < stride R := Nat.zero_lt_of_lt small
  have div : (f.val*stride R+r.val)/stride R = f.val := by
    rw [Nat.mul_comm f.val,Nat.mul_add_div pos,Nat.div_eq_of_lt small,Nat.add_zero]
  have mod : (f.val*stride R+r.val)%stride R=r.val := Nat.mul_add_mod_of_lt small
  simp only [mountHeader,fillSegment,headerBank,Nat.add_assoc,ite_eq_left bound,Nat.add_sub_cancel_left,
    div,mod,dite_eq_left f.isLt,dite_eq_left r.isLt,Fin.eta]

theorem Header.frame {order : Fin R ≃ Edges S h (2^W) k} {base attempts groupStart M : ℕ}
    {m m' : Memory w} (H : Header order base attempts groupStart M m)
    (keep : ∀ a,base≤ a → a< base+headerWords R → m' a=m a) :
    Header order base attempts groupStart M m' := fun f r =>
  (keep _ (header_cell base R f r).1 (header_cell base R f r).2).trans (H f r)

theorem mountHeader_outside (order : Fin R ≃ Edges S h (2^W) k) (base attempts groupStart M : ℕ)
    (m : Memory w) (a : ℕ) (out : a< base ∨ base+headerWords R≤ a) :
    mountHeader order base attempts groupStart M m a=m a := by
  simp [mountHeader,fillSegment,show ¬(base≤ a ∧ a< base+headerWords R) by omega]

def field (base R : ℕ) (f : Fin 10) : Expr := .lookup (headerBank base R f) .row

theorem Header.read {order : Fin R ≃ Edges S h (2^W) k} {base attempts groupStart M : ℕ}
    {m : Memory w} (H : Header order base attempts groupStart M m) (range : R≤2^w)
    (f : Fin 10) (r : Fin R) :
    (field base R f).eval m (r.val:Word w)=(recordWord attempts groupStart M (order r) f:Word w) := by
  have small : r.val< (headerBank base R f).size := r.isLt.trans (ProtocolRAMSupergroupDirectory.slotFits R)
  simp only [field,Expr.eval,Bank.read,Fin.val_cast_of_lt (r.isLt.trans_le range),Nat.mod_eq_of_lt small]
  exact H f r

end Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
end

end OAI
