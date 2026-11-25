import OAI.Hierarchy.DescentTerminalSliceRaw
import OAI.Hierarchy.DescentTerminalSliceClass
import OAI.Hierarchy.DescentTerminalRoleBirthWords
import OAI.Hierarchy.DescentPrimitivePaletteAllFit

namespace OAI
/-! # Reconstruct the six raw role fields from the original dated counters -/
namespace Hierarchy.DescentTerminalSliceRuns
open DescentSixParty DescentEpochTagKeys DescentBundleHistory DescentTerminalCombinedRole DescentPrimitivePalette
open DescentSIMDLookup DescentKernelHistory
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

variable {U:Type} {n A K p R M:ℕ}
def readSpans (count:ℕ) (header:Fin M→SliceCode) : List SliceCode :=
  List.ofFn fun j:Fin (min count M)=>header (j.castLE (Nat.min_le_right ..))

theorem readSpans_exact (actual:List SliceCode) (header:Fin M→SliceCode)
    (room:actual.length≤M) (source:∀j:Fin actual.length,header (j.castLE room)=actual[j.val]) :
    readSpans actual.length header=actual := by
  apply List.ext_getElem
  · simp [readSpans,Nat.min_eq_left room]
  · intro i old valid
    simp only [readSpans,List.getElem_ofFn]
    exact source ⟨i,valid⟩

def recover (dict:Codec U n) (kind:U→Layout) (token live:ℕ) (header:Fin M→SliceCode) :
    Arrays n A K p R :=
  if exists_:0<token ∧ token≤n then
    let u:=dict.read ⟨token-1,by omega⟩
    rawWords (n:=n) (p:=p) (R:=R) (birth (A:=A) (G:=K) dict u ((kind u).restore (readSpans live header)))
  else fun _=>0

theorem recover_read (dict:Codec U n) (kind:U→Layout) (u:U) (fits:dict.fits u)
    (xs:List (List SliceCode)) (shape:(kind u).correct xs)
    (positive:∀c∈xs.flatten,0<c.count) (header:Fin M→SliceCode)
    (bound:(repeatFields xs.flatten).length≤M)
    (stored:∀j:Fin (repeatFields xs.flatten).length,header (j.castLE bound)=(repeatFields xs.flatten)[j.val]) :
    recover (A:=A) (K:=K) (p:=p) (R:=R) dict kind ((dict.store u).val+1) (repeatFields xs.flatten).length header=
      rawWords (n:=n) (p:=p) (R:=R) (birth (A:=A) (G:=K) dict u xs) := by
  have token:0<(dict.store u).val+1 ∧ (dict.store u).val+1≤n:=⟨Nat.succ_pos _,(dict.store u).isLt⟩
  simp only [recover,dite_eq_left token,Nat.add_sub_cancel_right,Fin.eta,dict.read_store u fits,
    readSpans_exact _ header bound stored,Layout.restore_correct _ _ shape positive]

theorem recover_blank (dict:Codec U n) (kind:U→Layout) (total:ℕ) (header:Fin M→SliceCode) :
    recover (A:=A) (K:=K) (p:=p) (R:=R) dict kind 0 total header=fun _=>0:=by simp [recover]

variable {F:Type} [Field F] (G:PoweredGadget F) {s Z:ℕ} (op:DescentSixParty.RotorSpec)
local notation "dict" => DescentPrimitivePalette.codec (G:=G) (s:=s) (Z:=Z) op
local notation "colors" => DescentPrimitivePalette.colors G s Z op
def print (a k p R:ℕ) (input:Raw M) : Arrays colors a k p R :=
  recover dict (classify G p s) input.token input.live input.header

variable {T E:Type} {w:E→ℕ} {r:BitRecipe T E w} (hp:0<p) (sh:Shape p r) (u:r.Node)
variable (label:Label G s Z op) (shape:(classify G p s label).correct (sh.sliceFields u))
variable (input:Raw M) (tok:input.token=((DescentPrimitivePalette.codec (G:=G) (s:=s) (Z:=Z) op).store label).val+1)
    (pop:input.live=(repeatFields (sh.sliceFields u).flatten).length)
    (enough:(repeatFields (sh.sliceFields u).flatten).length≤M)
    (real:∀j:Fin (repeatFields (sh.sliceFields u).flatten).length,
      input.header (j.castLE enough)=(repeatFields (sh.sliceFields u).flatten)[j.val])
include hp shape tok pop enough real in
theorem printed_arrays (a k R:ℕ) :
    print G op a k p R input=rawWords (n:=colors) (p:=p) (R:=R) (birth (A:=a) (G:=k) dict label (sh.sliceFields u)) := by
  unfold print
  rw [tok,pop]
  exact recover_read _ _ _ (DescentPrimitivePalette.all_fit _ _) _ shape (used_slice p sh u hp) _ enough real

include hp shape tok pop enough in
theorem partial_arrays (a k R:ℕ)
    (onlyRotor:classify G p s label=.rotor→∀j:Fin (repeatFields (sh.sliceFields u).flatten).length,
      input.header (j.castLE enough)=(repeatFields (sh.sliceFields u).flatten)[j.val]) :
    print G op a k p R input=rawWords (n:=colors) (p:=p) (R:=R) (birth (A:=a) (G:=k) dict label (sh.sliceFields u)) := by
  have good:0<((dict).store label).val+1 ∧ ((dict).store label).val+1≤colors:=
    ⟨Nat.succ_pos _,((dict).store label).isLt⟩
  unfold print
  simp only [recover,tok,dite_eq_left good,Nat.add_sub_cancel_right,Fin.eta,
    (dict).read_store label (DescentPrimitivePalette.all_fit op label),pop]
  have restored : (classify G p s label).restore (readSpans (repeatFields (sh.sliceFields u).flatten).length input.header)=sh.sliceFields u := by
    apply Layout.restore_of_observations _ _ _ shape (used_slice p sh u hp)
    · simp [readSpans,Nat.min_eq_left enough]
    · exact fun hit=>readSpans_exact _ _ enough (onlyRotor hit)
  rw [restored]

end
end Hierarchy.DescentTerminalSliceRuns

end OAI
