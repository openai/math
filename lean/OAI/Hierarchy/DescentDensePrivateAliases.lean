import OAI.Hierarchy.DescentPackedPrivateAliases
import OAI.Hierarchy.DescentTerminalBirthOrdinal

namespace OAI
/-! # The dense restricted private number emitted by a packed local scalar book -/
namespace Hierarchy.DescentLocalPrivateNames
open DescentKernelHistory DescentSIMDLookup DescentTerminalChronologicalBooks
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {P Tag : Type} (r : Recipe Tag P) {a K : ℕ} (slot : Slot r↪Fin K)
    (code : r.UsedWord↪Cell a) (nz : ∀w,code w≠0)

def earlier (x : Fin K→Cell a) (j : ℕ) : Finset (Cell a) :=
  ((Finset.univ.filter (fun i : Fin K=>i.val<j)).image x).erase 0

include nz in
theorem earlier_raw (j : ℕ) : earlier (raw r slot code) j=
    (Finset.univ.filter fun w : r.UsedWord=>(firstAlias r slot w).val<j).image code := by
  ext c
  simp only [earlier,Finset.mem_erase,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨ne,i,hi,eqn⟩
    by_cases existsSlot : ∃s,slot s=i
    · obtain ⟨s,rfl⟩:=existsSlot
      rw [raw_read] at eqn
      cases h : read r s with
      | none=>exact False.elim (ne (by simpa [h] using eqn.symm))
      | some w=>
        exact ⟨w,lt_of_le_of_lt (firstAlias_le r slot s w h) hi,by simpa [h] using eqn⟩
    · exact False.elim (ne (by simpa [raw,existsSlot] using eqn.symm))
  · rintro ⟨w,lt,rfl⟩
    obtain ⟨s,e,hit⟩:=firstAlias_read r slot w
    exact ⟨nz w,slot s,e.symm ▸ lt,by simp [raw_read,hit]⟩

def denseDigit (x : Fin K→Cell a) (i : Fin K) : ℕ :=
  if x i=0 then 0 else 1+(earlier x (renameDigit x i-1)).card

include nz in
theorem denseDigit_read (s : Slot r) (w : r.UsedWord) (hit : read r s=some w) :
    denseDigit (raw r slot code) (slot s)=1+(ordinal ((firstAlias r slot).trans Fin.valEmbedding) w).val := by
  have nonzero : raw r slot code (slot s)≠0:=by simpa [raw_read,hit] using nz w
  rw [denseDigit,ite_eq_right nonzero,renameDigit_actual r slot code nz s w hit,Nat.add_sub_cancel_left,earlier_raw r slot code nz,
    Finset.card_image_of_injective _ code.injective,ordinal_val]
  rfl

theorem denseDigit_public (s : Slot r) (empty : read r s=none) : denseDigit (raw r slot code) (slot s)=0 := by
  simp [denseDigit,raw_read,empty]

theorem denseDigit_room (x : Fin K→Cell a) (i : Fin K) : denseDigit x i<K+1 := by
  unfold denseDigit
  split
  · omega
  next hi=>
    let hits:=Finset.univ.filter fun j=>x j=x i
    have first:=Finset.min'_mem hits (show hits.Nonempty from ⟨i,by simp [hits]⟩)
    have before : renameDigit x i-1<K := by
      simp only [renameDigit,ite_eq_right hi,Nat.add_sub_cancel_left]
      exact Fin.isLt _
    have card : (earlier x (renameDigit x i-1)).card≤renameDigit x i-1 := by
      let seen:=Finset.univ.filter fun j : Fin K=>j.val<renameDigit x i-1
      have clipped : seen.map Fin.valEmbedding⊆Finset.range (renameDigit x i-1) := by
        intro n h
        obtain ⟨u,hu,rfl⟩:=Finset.mem_map.mp h
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hu).2
      calc
        _≤(seen.image x).card := Finset.card_le_card (Finset.erase_subset _ _)
        _≤ seen.card := Finset.card_image_le
        _≤_ := by simpa using Finset.card_le_card clipped
    omega

def denseCell (a K : ℕ) (key : Cell (a*K)) : Cell (Nat.clog 2 (K+1)*K) :=
  encode (Nat.clog 2 (K+1)) K fun i=>⟨_,(denseDigit_room ((encode a K).symm key) i).trans_le (Nat.le_pow_clog (by decide) _)⟩

include nz in
theorem denseCell_read (s : Slot r) (w : r.UsedWord) (hit : read r s=some w) :
    digit (Nat.clog 2 (K+1)) (slot s).val (denseCell a K (encode a K (raw r slot code))).val=
      1+(ordinal ((firstAlias r slot).trans Fin.valEmbedding) w).val := by
  simpa only [denseCell,Equiv.symm_apply_apply,digit_encode] using denseDigit_read r slot code nz s w hit

theorem nativeDense (g : Banks) {M H t w out : ℕ}
    (room : Fits g (a*K) (Nat.clog 2 (K+1)*K) M H t w out) (x : Fin H→Fin t→Cell (a*K)) :
    (program g out H t M w).Spec (PinFrame (M:=M) g (denseCell a K) x)
      (fun m after=>after=ProtocolRAM.image out (H*chunks t M) (lookup g) m ∧
        ∀ row : Row H t M,after (out+(DescentSIMDLookup.row H t M row).val)=
          ((masked (denseCell a K) x row : ℕ) : Computability.VPVNP.BurstRAM.Word w))
      (4+(H*chunks t M)*(2*(lookup g).work+4)) ∧ ProtocolRAM.CheapCode (program g out H t M w) :=
  DescentSIMDLookup.spec g out room (denseCell a K) x

end
end Hierarchy.DescentLocalPrivateNames

end OAI
