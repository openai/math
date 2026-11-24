import OAI.Computability.VPVNP.PairNativeCacheRun
import OAI.Computability.VPVNP.LiveProgram

/-! # The native cache initializes the prescribed auxiliary leaf sources -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeCache

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM PrimedCounter.GuessWord
open LiveProgram LeafSourceLoad LeafRegisterBank LeafStartup NativeOperands
open CursorRouting CursorNetwork
open scoped Fin.CommRing

variable (c : Constants) {p : UniversalMachine.Program} {B n H : ℕ}
  {i : Fin (2^(n^c.chainPower-1))}
  (Q : Layout (CounterPublic.spec p c |>.lengths n i) n (addressWidth B n) H (CursorBounds.wordBits B n))
  (D : PrimedCounter.Data Q (n^(c.circuitExponent+5)))

/-- Cache preparation in the paper's actual eleven-operand row, using only
the runtime cache-base register, the fixed exponents, and the parsed prefix.
Each of the 38 private cells is exactly the scalar the virtual leaf reads. -/
theorem paper_run (a b : ℕ) (hb : 0 < b) (hB : 1 ≤ B) (hn : 2 ≤ n)
    (hH : H = 2^roundedUp a b n) (fit : PairNativeGeometry.Fits a b n (CursorBounds.wordBits B n))
    (hp : Q.program = p) (hbase : Q.scratchBase = 2^CursorBounds.virtualBits B n) (hf : D.Fits)
    (hroot : D.root.val = 0) (hw : 2 ≤ CursorBounds.wordBits B n)
    (hc : 2^CursorBounds.virtualBits B n*2^roundedUp 1 4 n < 2^CursorBounds.wordBits B n)
    {R pcs : ℕ} (reg : Fin (bankSize c) ↪ Fin R) (M : Machine (CursorBounds.wordBits B n) pcs R 11)
    (hpub : M.publicData = Pieces.word (AssemblerPublic.geometry B n H) (CounterPublic.actualPrefix p) ∘
      StageOperands.pair c)
    (embed : Fin (NativeCacheTable.size (code c a b reg)) → Fin pcs) (finish : Instr 2 pcs R 11)
    (rows : ∀ j, M.code (embed j) = (NativeCacheTable.row (code c a b reg) (storeSrc c reg)
      (ptr c reg) (one c reg) embed finish j).resize (CursorBounds.wordBits B n))
    (base : ℕ) (room : base+38 ≤ 2^(CursorBounds.wordBits B n)) (st : Config (CursorBounds.wordBits B n) pcs R)
    (entry : st.pc = embed (NativeCacheTable.label (code c a b reg) (code c a b reg).entry))
    (baseWord : st.reg (reg (saved (args c))) = (base : Word (CursorBounds.wordBits B n)))
    (v : Position (CursorBounds.virtualBits B n))
    (buf : Buffers (CursorBounds.virtualBits B n) (2^roundedUp 1 4 n) (CursorBounds.wordBits B n)) :
    let g := AssemblerPublic.geometry B n H
    let x := auxiliary D hw hc v buf
    ∃ t ≤ work (args c) a b g+76, ∃ out,
      Prefix M st (List.replicate t .tick) out ∧ out.pc = embed (NativeCacheTable.done (code c a b reg)) ∧
      Cached base out.privateMem (fun j : Static 34 => sourceWord x D.pub j.dest) ∧
      (∀ key : Word g.w, key.val < base ∨ base+38 ≤ key.val → out.privateMem key = st.privateMem key) ∧
      out.persistent = st.persistent ∧ ∀ j, j ∉ Set.range reg → out.reg j = st.reg j := by
  let g := AssemblerPublic.geometry B n H
  let lit := CounterPublic.actualPrefix p
  have h := paper_operands c Q D hB hn hp hbase hf hroot hw hc v buf
  have hfits j : FieldFits g (expr c j) := by
    have this := (h j).2
    cases he : expr c j with
    | geometry e => rwa [he] at this
    | prefixLength | prefixWord => trivial
  have h6 : (M.publicData 6).val = n := by
    rw [hpub]; exact Nat.mod_eq_of_lt (PrimedInputRAM.Opcodes.pubNat_lt Q hf.assembler 1)
  have h7 : (M.publicData 7).val = addressWidth B n := by
    rw [hpub]; exact Nat.mod_eq_of_lt (PrimedInputRAM.Opcodes.pubNat_lt Q hf.assembler 3)
  obtain ⟨t,ht,out,pre,stop,cache,rest,persistent,unchanged⟩ := run c g lit a b reg M hb (show 0 < n by omega) rfl
    hH fit hfits h6 h7 (by rw [hpub]; rfl) (by rw [hpub]; rfl) embed finish rows base room st entry baseWord
  exact ⟨t,ht,out,pre,stop,fun j => (cache j).trans (h j).1,rest,persistent,unchanged⟩

end PairSimulation.NativeCache

end VPVNP
end Computability
end OAI
