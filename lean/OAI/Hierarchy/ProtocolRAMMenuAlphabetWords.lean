import OAI.Hierarchy.ProbeStripMenu
import OAI.Hierarchy.ProtocolRAMVectorROMTable

namespace OAI
/-! # Public packet recommendation and selector-length words -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical
variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : A→E}
  {box : Set (E→ℝ)} {ε tree : ℝ} {N : ℕ}

def alphabetWord (m : Probe.FixedMenu F edge req box ε tree N) : ℕ → ℕ
  | 0 => 0
  | n+1 => if h : n < Fintype.card m.index then
      (m.packet ((Fintype.equivFin m.index).symm ⟨n,h⟩)).terms else 0

end Hierarchy.ProtocolRAM.StripDirectory

namespace Hierarchy.ProtocolRAM.Calendar.MenuROM
open Computability.VPVNP.BurstRAM PrivateRAM StripDirectory DiscrepancyROM
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical Fin.CommRing
variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : A→E}
  {box : Set (E→ℝ)} {ε tree : ℝ} {N w : ℕ}
  (menu : Probe.FixedMenu F edge req box ε tree N)

def recommendation (p : E→ℝ) :=
  if h : p∈box ∧ ε≤Probe.discrepancy F edge req p
  then (Fintype.equivFin menu.index (menu.select ⟨p,h⟩)).val+1 else 0

theorem recommendation_word {Y : Type*} (price : Y→E→ℝ) (legal : ∀ y,price y∈box) (y : Y) :
    recommendation menu (price y)=menu.word price legal y := by
  unfold recommendation Probe.FixedMenu.word
  by_cases failed : ε≤Probe.discrepancy F edge req (price y) <;> simp [legal,failed]

/-- All finite rounded price tuples have a definite packet code. An out-of-box
tuple in a malformed word produces zero. Every admitted tuple uses the
original compact catalogue's deterministic selector. -/
def menus {phases digits : ℕ} (base radix : ℕ)
    (price : Fin phases→(Fin digits→Fin radix)→E→ℝ) : Table phases digits :=
  ⟨base,radix,fun i v=>recommendation menu (price i v)⟩

def alphabets (base : ℕ) : Table 1 1 :=
  ⟨base,Fintype.card menu.index+1,fun _ key=>alphabetWord menu (key 0).val⟩

theorem alphabet_lookup (base : ℕ) (m : Memory w) (ready : (alphabets menu base).Resident m)
    (j : menu.index) :
    ((alphabets menu base).bank 0).read m (((Fintype.equivFin menu.index j).val+1:ℕ):Word w)=
      ((menu.packet j).terms:Word w) := by
  let a := Fintype.equivFin menu.index j
  let k : Fin 1 → Fin (Fintype.card menu.index+1) := fun _=>⟨a.val+1,Nat.succ_lt_succ a.isLt⟩
  have index : (finFunctionFinEquiv k).val=a.val+1 := by
    simp [k]
  have decoded : alphabetWord menu (a.val+1)=(menu.packet j).terms := by
    rw [alphabetWord,dite_eq_left a.isLt]
    exact congrArg (fun i=>(menu.packet i).terms) ((Fintype.equivFin menu.index).symm_apply_apply j)
  calc
    _ = ((alphabets menu base).bank 0).read m ((finFunctionFinEquiv k).val : Word w) :=
      congrArg (fun n : ℕ => ((alphabets menu base).bank 0).read m (n : Word w)) index.symm
    _ = _ := (ready 0 k).trans (congrArg (fun n : ℕ => (n : Word w)) decoded)

end Hierarchy.ProtocolRAM.Calendar.MenuROM
end

end OAI
