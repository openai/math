import OAI.ThreeFlat.Diagonal.TraceSourceOwner
import OAI.ThreeFlat.Diagonal.TraceSourceFibers
import OAI.ThreeFlat.Diagonal.TraceStaticLayout

namespace OAI
/-! # Source owner and local hidden reservation on the assembled static gate layout -/

namespace ThreeFlat.Diagonal.TraceSourceOwner

open Computability.VPVNP BurstRAM LaneCursor TraceStaticRow TraceUniformRow TracePhysical
variable {F : Type*} {w p S f lane low n c : ℕ}

private theorem indexed_hidden {t b q P o : ℕ} (ht : t=2^lane*2^low)
    (rows : Fin t → Fin c → TraceCircuit.Cell F n q) (inp : Fin t → Fin q → BitSource b P)
    (hidden : Fin b → Row lane low) (pins : Fin P → Row lane low)
    (off : Fin o → Row lane low) (base : Fin o) (hbase : (off base).val=0)
    (idx : Fin t → Fin q → Fin o) (ok : ∀ v j,
      v.cast ht = partner (sourceRow hidden pins (v.cast ht) (inp v j)) (off (idx v j)))
    (i : Fin (b+t*n)) :
    (indexedLayout ht rows inp hidden pins off base hbase idx ok).hiddenRow i =
      TraceCircuit.blockHiddenRow hidden (i.cast (by rw [ht])) := by subst t; rfl

section
variable [CommRing F] [Fintype F]
variable (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k : ℕ)
    (fit : S+f ≤ 2^(1+(lane+low)))

set_option quotPrecheck false
local notation "dsc" => shape w p r k S f (lane+low) (gateTable hF hw hp base f st r k (lane+low)).internal
local notation "site" => layout hF hw hp base st hs hf r k fit
local notation "net" => network hF hw hp base st hs hf r k (lane+low)

include hF hw hp base st hs hf r k fit in
theorem layout_hidden (i : Fin (net).internal) :
    ((site).hiddenRow i).val = (locate dsc i.val).1 := by
  unfold TraceStaticRow.layout
  erw [indexed_hidden]
  exact (block_hidden fit _).symm

include hF hw hp base st hs hf r k fit in
theorem layout_source (v : Row lane low) (z : BitSource (net).internal (S*w)) :
    (sourceRow (site).hiddenRow (site).pinRow v z).val =
      ownerNat w p r k S f (lane+low) (gateTable hF hw hp base f st r k (lane+low)).internal
        v.val (RAM.BitLayout.sourceAddress z) := by
  cases z with
  | constant b => cases b <;> simp [ownerNat,appendAt,sourceRow,RAM.BitLayout.sourceAddress]
  | hidden h =>
    rw [sourceRow,layout_hidden]
    simp [ownerNat,RAM.BitLayout.sourceAddress,RAM.BitLayout.hiddenBase,Nat.add_assoc]
  | pin j =>
    rw [sourceRow,TraceStaticRow.layout_pin]
    simp only [ownerNat,RAM.BitLayout.sourceAddress,appendAt_right,appendAt_left _ _ j.isLt]
    rfl

include hF hw hp base st hs hf r k fit in
theorem staticPin_lane (L : Lane lane) (j : Fin (S*w)) :
    (splitRow _ _ ((site).pinRow j)).1=L ↔ j.val/pinSpan w low=(finFunctionFinEquiv L).val := by
  rw [lane_eq_iff,TraceStaticRow.layout_pin]
  change j.val/w/2/2^low=_ ↔ _
  simp [pinSpan,Nat.div_div_eq_div_mul]

include hF hw hp base st hs hf r k fit in
def staticExt (L : Lane lane) : Fin (pinCount S w low (finFunctionFinEquiv L).val) ≃
    {j : Fin (S*w) // (splitRow _ _ ((site).pinRow j)).1=L} :=
  (pinFiber S w low _).trans (Equiv.subtypeEquivRight (fun j =>
    (staticPin_lane hF hw hp base st hs hf r k fit L j).symm))

include hF hw hp base st hs hf r k fit in
theorem staticHidden_lane (L : Lane lane) (i : Fin (net).internal) :
    (splitRow _ _ ((site).hiddenRow i)).1=L ↔ (locate dsc i.val).1/2^low=(finFunctionFinEquiv L).val := by
  rw [lane_eq_iff,layout_hidden]

include hF hw hp base st hs hf r k in
theorem hidden_count : (net).internal=(dsc).count := by
  change (Fintype.card (TracePhysical.Shared w r f (lane+low))+_)+_=_
  rw [shared_card w p r k S f (lane+low) 0]
  dsimp only [Shape.count,shape,Shape.track,CopyCount]
  omega

include hF hw hp base st hs hf r k fit in
noncomputable def staticHidden (L : Lane lane) :
    {h : Fin (net).internal // (splitRow _ _ ((site).hiddenRow h)).1=L} ↪ Fin (2^low*(dsc).stride) := by
  have hfit : (dsc).header+(dsc).ticks ≤ 2*(dsc).rows := by simpa [shape,pow_succ,pow_add] using fit
  let pack := hiddenFiber dsc hfit low (finFunctionFinEquiv L).val
  let inc : {h : Fin (net).internal // (splitRow _ _ ((site).hiddenRow h)).1=L} →
      {h : Fin (dsc).count // (locate dsc h.val).1/2^low=(finFunctionFinEquiv L).val} :=
    fun h => ⟨h.val.cast (hidden_count hF hw hp base st hs hf r k),
      (staticHidden_lane hF hw hp base st hs hf r k fit L h.val).1 h.property⟩
  exact ⟨pack ∘ inc,fun _ _ e => Subtype.ext (Fin.ext (congrArg (fun x => x.val.val) (pack.injective e)))⟩

end
end ThreeFlat.Diagonal.TraceSourceOwner

end OAI
