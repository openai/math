import OAI.Hierarchy.DescentTerminalChipRuntime
import OAI.Hierarchy.DescentDatedAddressBook

namespace OAI
/-! # The terminal five physical scans following the home and emitter shelves -/
namespace Hierarchy.DescentTerminalChipRuntime.Dated
open ProtocolRAM Computability.VPVNP.BurstRAM ThreeFlat.RAM

def placed (first rows : ℕ) : Layout := ⟨first,Nat.clog 2 rows⟩
def words (rows slots : ℕ) := 4*2^Nat.clog 2 rows+2+slots

theorem terminal_end (first rows slots : ℕ) :
    (placed first rows).keys+slots=first+words rows slots := by
  simp [placed,Layout.keys,Layout.width,words,Nat.add_assoc]

theorem words_le (rows slots : ℕ) : words rows slots≤8*rows+6+slots := by
  have pad : 2^Nat.clog 2 rows≤2*rows+1 := by
    cases eqn : Nat.clog 2 rows with
    | zero => simp []
    | succ t =>
      have near := Nat.pow_lt_of_lt_clog (show t < Nat.clog 2 rows by omega)
      simp only [pow_succ]
      omega
  unfold words
  omega

theorem room (first rows slots w : ℕ) (b : Banks)
    (denseInput : (dense b).Fits w first) (routeInput : (route b).Fits w first)
    (keyInput : (key b).Fits w first) (x : b.xWords.Fits w first) (y : b.ySlices.Fits w first)
    (xRows : rows≤b.xWords.size) (yRows : rows≤b.ySlices.size)
    (top : first+words rows slots<2^w) : Room (placed first rows) b w rows slots :=
  ⟨denseInput,routeInput,keyInput,x,y,xRows,yRows,Nat.le_pow_clog (by decide) _,
    (terminal_end first rows slots).trans_lt top⟩

private theorem image_before (base n : ℕ) (e : Expr) {w : ℕ} (m : Memory w) {x : ℕ}
    (before : x<base) : image base n e m x=m x := by
  simp [image,fillSegment,Nat.not_le.mpr before]

theorem retained (first rows slots : ℕ) (b : Banks) {w : ℕ} (m : Memory w) {x : ℕ} (old : x<first) :
    finalMem (placed first rows) b rows slots m x=m x := by
  let A:=placed first rows
  have earlier : x<A.x.base ∧ x<A.xCheck ∧ x<A.y.base ∧ x<A.yCheck ∧ x<A.keys := by
    dsimp only [A,placed,Layout.x,Layout.xCheck,Layout.y,Layout.yCheck,Layout.keys]
    omega
  change finalMem A b rows slots m x=_
  calc
    _ = m₄ A b rows m x := image_before A.keys slots (key b) (m₄ A b rows m) earlier.2.2.2.2
    _ = m₃ A b rows m x :=
      DescentTerminalProposalCheck.frame (n:=rows) A.y b.ySlices (m₃ A b rows m) earlier.2.2.2.1
    _ = m₂ A b rows m x := image_before A.y.base rows (route b) (m₂ A b rows m) earlier.2.2.1
    _ = m₁ A b rows m x :=
      DescentTerminalProposalCheck.frame (n:=rows) A.x b.xWords (m₁ A b rows m) earlier.2.1
    _ = m x := image_before A.x.base rows (dense b) m earlier.1

end Hierarchy.DescentTerminalChipRuntime.Dated

end OAI
