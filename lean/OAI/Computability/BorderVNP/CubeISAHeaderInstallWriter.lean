import OAI.Computability.BorderVNP.CubeISAHeaderInstallSetup
import OAI.Computability.BorderVNP.PackedDirectoryWriter

/-! # Writing the thirteen static fields into physical memory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeHeaderInstall

open VPVNP.BurstRAM Packing.Directory.ISA

/-- Registers in the order used by the decoder of the secondary header. -/
def columns : List Reg := [21,22,23,24,25,26,27,28,29,30,31,32,33]

/-- All thirteen stores give exactly the specified secondary memory image. -/
theorem write_run {w n bits : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Inputs) (fit : l.Fits w n bits (readings pub 0))
    (st : Static l (readings s)) (vol : readings s 27 = l.volume n bits)
    (cw : readings s 31 = Nat.clog 2 l.a) (rw : readings s 32 = Nat.clog 2 (l.cap+1)) :
    BoundedRun pub mac (pushWords columns) s m 27 (fun z => z.mem = l.image n bits (readings m)) := by
  have room : l.header+13 < 2^w := by have h := fit.bank; unfold Inputs.packetBase at h; omega
  have h20 : s 20 = DiagonalResidueRAM.word w l.header := Fin.ext <| st.header.trans
    (DiagonalResidueRAM.word_val _ _ (by omega)).symm
  have hw : 1 < 2^w := by omega
  have h1 : s 1 = 1 := Fin.ext <| st.one.trans (by simp [Nat.mod_eq_of_lt hw])
  obtain ⟨es,run,cost⟩ := pushWords_runs pub mac columns s m l.header h20 h1 room (by decide)
  refine ⟨es,_,_,run,cost.le,?_⟩
  change readings (putWords m l.header (columns.map s)) = _
  funext addr
  by_cases h : l.header ≤ addr ∧ addr < l.header+13
  · simp only [Inputs.image, h]
    let i : Fin (columns.map s).length := ⟨addr-l.header,by change _ < 13; omega⟩
    have hi : l.header+i.val = addr := by dsimp [i]; omega
    have read := putWords_read m l.header (columns.map s) i
    rw [hi] at read
    change (putWords m l.header (columns.map s) addr).val = _
    rw [read]
    change ((columns.map s)[i.val]).val = l.value n bits i.val
    generalize i = k
    obtain ⟨k,hk⟩ := k
    change k < 13 at hk
    rcases st with ⟨_,_,h21,h22,h23,h24,h25,h26,h28,h29,h30,h33⟩
    change (s _).val = _ at h21 h22 h23 h24 h25 h26 h28 h29 h30 h33 vol cw rw
    interval_cases k <;> simp [columns,Inputs.value, *]
  · simp only [Inputs.image, h, ite_false,readings]
    rw [putWords_outside _ _ _ _ (by change addr < l.header ∨ l.header+13 ≤ addr; omega)]

end RoutingISA.CubeHeaderInstall

end BorderVNP
end Computability
end OAI
