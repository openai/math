import OAI.Hierarchy.GridSelector
import OAI.ThreeFlat.RAM.TerminalWireArchive
import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # Native check for the live end and all remaining selector padding

The shared terminal bits occupy an address interval immediately after the
decoded history prefix. Both terminal-bank operands refer to the same
selector; the native row checker verifies all the zero padding from the
reported live end and preserves the input memory. -/

namespace Hierarchy.GridSelector
open ThreeFlat
open Diagonal.HistoryContraction Computability.VPVNP.BurstRAM RAM
open scoped Classical

/-- All and only the coordinates beyond the live end must vanish. -/
theorem padded_iff (l : List Bool) {lo len : ℕ} (size : l.length=len) :
    l.drop lo=List.replicate (len-lo) false ↔
      ∀ i : Fin len, lo ≤ i.val → l[i.val]'(by omega)=false := by
  constructor
  · intro eq i hi
    let j := i.val-lo
    have ji : j < (l.drop lo).length := by simp only [List.length_drop,size]; dsimp [j]; omega
    have pos : lo+j=i.val := by dsimp [j]; omega
    have g := List.getElem_of_eq eq ji
    simpa [List.getElem_drop,pos] using g
  · intro h
    apply List.ext_getElem
    · simp [size]
    · intro i hi hj
      have room : lo+i<len := by simp only [List.length_drop,size] at hi; omega
      simpa [List.getElem_drop] using h ⟨lo+i,room⟩ (Nat.le_add_right _ _)

def layout (current suffixInfo raw cap : ℕ) : TerminalWireArchive.Layout :=
  ⟨current,current,raw,raw,cap,0,0,suffixInfo⟩

/-- Link the natural parser condition on the selector reached after Plan.read
to the stored words examined by the native checker. -/
theorem canonical_iff {W cap lo : ℕ} (wpos : 0<W) (current info raw : ℕ)
    (m : Memory W) (l : List Bool) (size : l.length=cap)
    (endWord : (m info).val=lo) (read : ∀ i : Fin cap,
      m (raw+i.val)=BitLayout.bitWord W (l[i.val]'(by omega))) :
    TerminalWireArchive.canonical (layout current info raw cap) m ↔
      lo≤cap ∧ l.drop lo=List.replicate (cap-lo) false := by
  rw [padded_iff l size]
  unfold TerminalWireArchive.canonical layout
  simp only [Nat.add_zero,endWord,ite_self]
  have zero (i : Fin cap) : m (raw+i.val)=0 ↔ l[i.val]'(by omega)=false := by
    rw [read]
    cases b : l[i.val]'(by omega) <;> simp [BitLayout.bitWord,wpos.ne']
  refine and_congr_right fun _ => ⟨fun g i hi => (zero i).mp (g _ hi i.isLt),?_⟩
  exact fun g i hi he => (zero ⟨i,he⟩).mpr (g ⟨i,he⟩ hi)

/-- A stage that already read the history needs then to check only this
fixed native suffix procedure. Each bit is visited once. On malformed
padding all further fuel contributes zero in every semiring. -/
theorem check_padding {W cap lo : ℕ} (wpos : 0<W) (current info raw : ℕ)
    {F : Type*} [Semiring F] (field : FieldCode F W) (m : Memory W)
    (l : List Bool) (size : l.length=cap)
    (endWord : (m info).val=lo) (read : ∀ i : Fin cap,
      m (raw+i.val)=BitLayout.bitWord W (l[i.val]'(by omega)))
    (room : TerminalWireArchive.Bounds (layout current info raw cap) W)
    (limit : (m (m current).val).val=cap+1) :
    let x := layout current info raw cap
    TickStageSpec.Admission field (TerminalWireArchive.check (W:=W) x).block
      (TerminalWireArchive.check x).publicData (·=m)
      (fun _ => lo≤cap ∧ l.drop lo=List.replicate (cap-lo) false) (fun old out => out=old)
      (6+(cap+1)*(2*(TerminalWireArchive.checkWord x).work+4)) := by
  intro x P R K M pc reg pub exit inst data c mem start same
  subst mem
  have t := TerminalWireArchive.check_steps field x room M pc reg pub exit inst data c m start limit
  exact ⟨fun ok => t.1 ((canonical_iff wpos current info raw m l size endWord read).2 ok),
    fun no => t.2 (no ∘ (canonical_iff wpos current info raw m l size endWord read).1)⟩

end Hierarchy.GridSelector

end OAI
