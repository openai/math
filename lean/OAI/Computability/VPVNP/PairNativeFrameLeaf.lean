import OAI.Computability.VPVNP.PairNativeFrameRun
import OAI.Computability.VPVNP.PairSimulationLeafGeometryLoad

/-! # Reading the leaf's fixed operands from the installed geometry

The native vertex uses twelve fields. Each visit reloads the first ten,
in the order required by the leaf decoder and route test.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeFrame
open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- First ten words of the installed frame, in the order used to reload the leaf decoder and
route-test operands. -/
def leafWords (degree : ℕ) (pub : Fin 11 → Word w) (header role : Word w) (m : Memory w) :
    Fin 10 → Word w := fun j => fields degree pub header role m (j.castLE (by decide))

theorem Result.stored {P : Ports r} {degree : ℕ} {pub : Fin 11 → Word w} {m : Memory w} {c out : Config w p r}
    (h : Result P degree pub m c out) :
    LeafGeometryLoad.Stored (pub 6).val (frameBase (fromHeader degree pub (c.reg P.header) m)) out.privateMem
      (leafWords degree pub (c.reg P.header) (c.reg P.role) m) := by
  refine ⟨?_,fun i => h.values (i.castLE (by decide))⟩
  rw [Fin.cast_val_eq_self]; exact h.pointer

/-- Any subsequent writes restricted to the operand cache or above it
preserve the actual geometry record. The role and histogram words are
also protected by the same two address inequalities. -/
theorem Result.stored_after {P : Ports r} {degree : ℕ} {pub : Fin 11 → Word w} {m : Memory w}
    {c out : Config w p r} (h : Result P degree pub m c out) (priv : Word w → Word w)
    (head : (pub 6).val < (fromHeader degree pub (c.reg P.header) m).cacheBase)
    (bank : frameBase (fromHeader degree pub (c.reg P.header) m)+12 ≤ (fromHeader degree pub (c.reg P.header) m).cacheBase)
    (fit : (fromHeader degree pub (c.reg P.header) m).cacheBase ≤ 2^w)
    (same : ∀ j : Word w, j.val < (fromHeader degree pub (c.reg P.header) m).cacheBase → priv j = out.privateMem j) :
    LeafGeometryLoad.Stored (pub 6).val (frameBase (fromHeader degree pub (c.reg P.header) m)) priv
      (leafWords degree pub (c.reg P.header) (c.reg P.role) m) ∧
    ∀ i : Fin 12, priv ((frameBase (fromHeader degree pub (c.reg P.header) m)+i.val : ℕ) : Word w) =
      fields degree pub (c.reg P.header) (c.reg P.role) m i := by
  have full (i : Fin 12) := h.values i
  have field (i : Fin 12) : priv ((frameBase (fromHeader degree pub (c.reg P.header) m)+i.val : ℕ) : Word w) =
      fields degree pub (c.reg P.header) (c.reg P.role) m i := by
    rw [same,full]
    rw [Fin.val_natCast,Nat.mod_eq_of_lt (by have := i.isLt; omega)]
    have := i.isLt; omega
  refine ⟨⟨?_,fun i => field (i.castLE (by decide))⟩,field⟩
  rw [Fin.cast_val_eq_self,same _ head]; exact h.pointer

variable {L : PrimedInputRAM.Lengths} {n a H s : ℕ} {Q : PrimedInputRAM.Layout L n a H w}

/-- The terminal descriptor's preserved geometry and the concrete shadow
contents supply the nine obligations of the executable leaf front. -/
theorem leaf_operands (degree : ℕ) (pub : Fin 11 → Word w) (header role : Word w) (m : Memory w)
    (pc : LeafImage.Label → Fin p) (reg : LeafImage.Reg ↪ Fin r) (operand : LeafImage.Pub → Fin k)
    (ret : Fin p) (M : Machine w p r k)
    (assigned : M.publicData ∘ operand = leafWords degree pub header role m ∘ LeafGeometryLoad.slot)
    (data : PrimedCounter.Data Q s) (b l cap : ℕ)
    (rowStride : (m (header+15).val).val = cap+2)
    (radixB : (m (header+18).val).val = 2^b) (radixL : (m (header+19).val).val = 2^l)
    (span : (m (header+20).val).val = LiveAuxiliaryHeaders.span L data.hist.length)
    (fits : (pub 3).val+(m (header+20).val).val ≤ 2^w)
    (shadow : ∀ i < (m (header+20).val).val, (m ((pub 3).val+i)).val = (data.initial i).val)
    (length : (pub 6).val = n) :
    LeafFront.Operands (LeafImage.front pc reg operand ret) M m data (fromHeader degree pub header m) b l cap ∧
    M.publicData (operand .size) = (n : Word w) := by
  let val := leafWords degree pub header role m
  have address (j : LeafAddress.Field) : M.publicData (operand (.address j)) = val (LeafGeometryLoad.slot (.address j)) :=
    congrFun assigned (.address j)
  have arena (j : RoutePrepare.Field) : M.publicData (operand (.arena j)) = val (LeafGeometryLoad.slot (.arena j)) :=
    congrFun assigned (.arena j)
  have hn : (pub 6).val = (fromHeader degree pub header m).arguments.start := rfl
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,arena .stride,arena .cache⟩,?_⟩
  · exact (congrArg Fin.val (address .stride)).trans rowStride
  · exact (congrArg Fin.val (address .radixB)).trans radixB
  · exact (congrArg Fin.val (address .radixL)).trans radixL
  · exact (congrArg Fin.val (address .span)).trans span
  · change (M.publicData (operand (.address .shadow))).val+(M.publicData (operand (.address .span))).val ≤ _
    rw [address .shadow,address .span]; exact fits
  · change ∀ i < (M.publicData (operand (.address .span))).val, (m ((M.publicData (operand (.address .shadow))).val+i)).val = _
    rw [address .shadow,address .span]; exact shadow
  · exact (arena .start).trans ((Fin.cast_val_eq_self (pub 6)).symm.trans (congrArg (fun x : ℕ => (x : Word w)) hn))
  · exact (congrFun assigned .size).trans ((Fin.cast_val_eq_self (pub 6)).symm.trans (congrArg (fun x : ℕ => (x : Word w)) length))

end PairSimulation.NativeFrame

end VPVNP
end Computability
end OAI
