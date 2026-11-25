import OAI.Hierarchy.DescentLocalPrivateNames
import OAI.Hierarchy.DescentPackingOrdinals

namespace OAI
/-! # Packed first-use aliases in genuine local scalar-node order -/

namespace Hierarchy.DescentLocalPrivateNames
open DescentSIMDLookup DescentKernelHistory
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {Tag B : Type} (r : Recipe Tag B) {a K : ℕ}

/-- Existing scalar birth order followed by the actual argument ordinal. -/
def orderedSlots (birth : r.Node↪ℕ) (room : Fintype.card (Slot r)≤K) : Slot r↪Fin K :=
  (DescentPacking.orderedUnits r.arity birth birth.injective).toEmbedding.trans
    (Fin.castLEEmb room)

theorem orderedSlots_val (birth : r.Node↪ℕ) (room : Fintype.card (Slot r)≤K) (s : Slot r) :
    (orderedSlots r birth room s).val=ProtocolRAMPortRanks.«prefix» r.arity birth s.1+s.2.val := rfl

/-- A fixed finite table simultaneously gives every occupied argument the first
local occurrence of its own private label. The public and empty positions are zero. -/
def renameCell (a K : ℕ) (key : Cell (a*K)) : Cell (Nat.clog 2 (K+1)*K) :=
  let data:=(encode a K).symm key
  encode (Nat.clog 2 (K+1)) K (fun i=>⟨renameDigit data i,by
    have ceiling : K+1≤2^Nat.clog 2 (K+1):=Nat.le_pow_clog (by decide) _
    unfold renameDigit
    split
    · positivity
    · have bound (j : Fin K) : 1+j.val<K+1:=by omega
      apply lt_of_lt_of_le (bound _) ceiling⟩)

theorem renameCell_read (slot : Slot r↪Fin K) (code : r.UsedWord↪Cell a)
    (nz : ∀h,code h≠0) (s : Slot r) (h : r.UsedWord) (uses : read r s=some h) :
    digit (Nat.clog 2 (K+1)) (slot s).val
      (renameCell a K (encode a K (raw r slot code))).val=1+(firstAlias r slot h).val := by
  simp only [renameCell,Equiv.symm_apply_apply,digit_encode]
  exact renameDigit_actual r slot code nz s h uses

theorem renameCell_public (slot : Slot r↪Fin K) (code : r.UsedWord↪Cell a)
    (s : Slot r) (pub : read r s=none) :
    digit (Nat.clog 2 (K+1)) (slot s).val
      (renameCell a K (encode a K (raw r slot code))).val=0 := by
  simp [renameCell,digit_encode,renameDigit,raw_read,pub]

theorem nativeAliases (g : Banks) {M H t w out : ℕ}
    (room : Fits g (a*K) (Nat.clog 2 (K+1)*K) M H t w out)
    (x : Fin H→Fin t→Cell (a*K)) :
    (program g out H t M w).Spec (PinFrame (M:=M) g (renameCell a K) x)
      (fun m after=>after=ProtocolRAM.image out (H*chunks t M) (lookup g) m ∧
        ∀ row : Row H t M,after (out+(DescentSIMDLookup.row H t M row).val)=
          ((masked (renameCell a K) x row : ℕ) : Computability.VPVNP.BurstRAM.Word w))
      (4+(H*chunks t M)*(2*(lookup g).work+4)) ∧ ProtocolRAM.CheapCode (program g out H t M w) :=
  DescentSIMDLookup.spec g out room (renameCell a K) x

end
end Hierarchy.DescentLocalPrivateNames

end OAI
