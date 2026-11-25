import OAI.ThreeFlat.RAM.TickPaddedROM

namespace OAI
/-! # Physical effect of the linked padding and shared library bank -/

namespace ThreeFlat.RAM.TickPaddedROM
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr ContinuationLink HistoryFactors BitLayout Diagonal.TraceCircuit
open scoped Fin.CommRing

variable {F : Type*} [Zero F] [One F] {w k pc reg pins : ℕ}

-- Installation transports the already emitted instruction. Keep the two instruction
-- constructors opaque while normalizing their program-counter embeddings.
attribute [local irreducible] TickGenerateTable.emit HistoryPadROM.emit TickLUTSeed.expr
  HistoryPadDriver.term

omit [Zero F] [One F] in
private theorem table_fetch {t : ℕ} (M : Machine w pc reg k) (code : FieldCode F w)
    (table : Fin t→(Fin 3→Bool)→F) (lut : ℕ) (loc : Fin (labels t) ↪ Fin pc)
    (regs : Fin (4+binds t) ↪ Fin reg) (pub : Fin 0→Fin k) (exit : Fin pc)
    (rom : (tableBlock code table lut).Installed M loc regs pub exit)
    (i : Fin ((TickLUTSeed.expr (k:=k) code table lut).labels+6)) :
    let e:=TickLUTSeed.expr (k:=k) code table lut
    let h:=tableLabels (k:=k) code table lut
    let f:=fun j=>loc (Fin.cast h j)
    let frame:=(finCongr (tableRegs (k:=k) code table lut)).toEmbedding.trans regs
    M.code (f i)=TickGenerateTable.emit e (lut : Word w) (lut+8*t : ℕ) f frame exit i := by
  intro e h f frame
  have fetched:=rom (Fin.cast h i)
  simpa only [tableBlock,e,h,f,frame,Fin.cast_cast,Fin.cast_refl,id_eq] using fetched

private theorem pad_fetch (M : Machine w pc reg k) (last : ℕ) (loc : Fin 96 ↪ Fin pc)
    (regs : Fin 33 ↪ Fin reg) (pub : Fin 1→Fin k) (exit : Fin pc)
    (rom : (padBlock w last).Installed M loc regs pub exit)
    (i : Fin (HistoryPadROM.count (w:=w) (pub 0))) :
    let base:=pub 0
    let h:=padLabels (w:=w) base
    let f:=fun j=>loc (Fin.cast h j)
    let frame:=(finCongr (padRegs (w:=w) base)).toEmbedding.trans regs
    M.code (f i)=HistoryPadROM.emit base (last : Word w) f frame exit i := by
  intro base h f frame
  have fetched:=rom (Fin.cast h i)
  simpa only [padBlock,base,h,f,frame,Fin.cast_cast,Fin.cast_refl,id_eq] using fetched

set_option maxHeartbeats 4000000 in
/-- All genuine four-word records use the same constant coefficient library.
The upper metadata endpoint is fixed by the padded row count. -/
theorem advance_bank (code : FieldCode F w) (N : BitNetwork F pins) (L : Library N)
    (b u metadata lut : ℕ) (M : Machine w pc reg k) (base : Fin k)
    (P : Fin (labels (L.count+2)+96) ↪ Fin pc)
    (R : Fin (max (4+binds (L.count+2)) 33) ↪ Fin reg) (exit : Fin pc)
    (rom : (block code (L.padded b u).table lut (metadata+4*N.cells+4*(b+u))).Installed
      M P R (fun _ => base) exit)
    (c : Config w pc reg) (m : Memory w)
    (start : c.pc = P (block code (L.padded b u).table lut (metadata+4*N.cells+4*(b+u))).first)
    (safe : metadata+4*N.cells+4*(b+u) ≤ lut) (fit : lut+8*(L.count+2) < 2^w)
    (header : ∀ j : Fin 4, HistoryPadDriver.header (M.publicData base) m j =
      ![(metadata+4*N.cells : ℕ),(b : Word w),(hiddenBase pins+N.internal : ℕ),(L.count : Word w)] j)
    (away : ∀ j : Fin 4, (M.publicData base+(j.val : Word w)).val < metadata+4*N.cells ∨
      lut+8*(L.count+2) ≤ (M.publicData base+(j.val : Word w)).val)
    (rows : ∀ i : Fin N.cells, ∀ j : Fin 4, m (metadata+4*i.val+j.val) = metadataWord L i j) :
    ∃ t ≤ (4+8*(L.count+2)*(6*(8*(L.count+2))+10))+(5+62*(4*(b+u))),
      ∃ out : Config w pc reg, ∃ result : Memory w, out.pc=exit ∧
        advance M.program t c m = some (out,result) ∧
        Stores (addPadding N b u) (L.padded b u) code metadata lut result ∧
        ∀ i < metadata, result i = m i := by
  let t := (L.padded b u).count
  have tCount : (L.padded b u).count=L.count+2 := rfl
  let T := (L.padded b u).table
  let last := metadata+4*N.cells+4*(b+u)
  let h1 := tableLabels (k:=k) code T lut
  let h2 := tableRegs (k:=k) code T lut
  let hs := padLabels (w:=w) base
  let hr := padRegs (w:=w) base
  let padPC := fun i => ((Fin.natAddEmb (labels t)).trans P) (Fin.cast hs i)
  let seedPC := fun i => ((Fin.castAddEmb 96).trans P) (Fin.cast h1 i)
  let pr := (finCongr hr).toEmbedding.trans ((Fin.castLEEmb (le_max_right (4+binds t) 33)).trans R)
  let sr := (finCongr h2).toEmbedding.trans ((Fin.castLEEmb (le_max_left (4+binds t) 33)).trans R)
  have padEntry : HistoryPadROM.setup (w:=w) base padPC 0 = P (Fin.natAdd (labels t) 94) := by
    apply congrArg P
    apply Fin.ext
    change labels t+((HistoryPadDriver.term (w:=w) base).labels+6+0) = labels t+94
    rw [Term.labels_eq,HistoryPadDriver.term_binds]
  let seedFrame:=Fin.castLEEmb (le_max_left (4+binds t) 33)
  let padFrame:=Fin.castLEEmb (le_max_right (4+binds t) 33)
  let pubMap:=fun _ : Fin 1 => base
  let seed:=(tableBlock code T lut).reindex seedFrame (Fin.elim0 : Fin 0→Fin 1)
  let pad:=(padBlock w last).reindex padFrame (id : Fin 1→Fin 1)
  have installed : (seed.seq pad).Installed M P R pubMap exit := rom
  obtain ⟨a,b'⟩ := (Block.seq_installed seed pad M P R pubMap exit).mp installed
  have seedROM := (Block.reindex_installed (tableBlock code T lut) seedFrame
    (Fin.elim0 : Fin 0→Fin 1) M ((Fin.castAddEmb 96).trans P) R pubMap
    (P (Fin.natAdd (labels t) pad.first))).mp a
  have padROM := (Block.reindex_installed (padBlock w last) padFrame id M
    ((Fin.natAddEmb (labels t)).trans P) R pubMap exit).mp b'
  apply TickPaddedTail.generate M code N L b u metadata lut base padPC pr seedPC sr exit m c
  · intro i
    rw [padEntry]
    let loc:=(Fin.castAddEmb 96).trans P
    let frame:=(Fin.castLEEmb (le_max_left (4+binds t) 33)).trans R
    let next:=P (Fin.natAdd (labels t) 94)
    calc
      M.code (seedPC i) = TickGenerateTable.emit (TickLUTSeed.expr code T lut) (lut : Word w)
          (lut+8*t : ℕ) seedPC sr next i :=
        table_fetch M code T lut loc frame (pubMap ∘ Fin.elim0) next seedROM i
      _ = _ := congrArg (fun n : ℕ => TickGenerateTable.emit (TickLUTSeed.expr code T lut)
        (lut : Word w) (lut+8*n : ℕ) seedPC sr next i) tCount
  · intro i
    let loc:=(Fin.natAddEmb (labels t)).trans P
    let frame:=(Fin.castLEEmb (le_max_right (4+binds t) 33)).trans R
    exact pad_fetch M last loc frame (pubMap ∘ id) exit padROM i
  · rw [start]
    apply congrArg P
    apply Fin.ext
    change 3*(binds t)+1=(TickLUTSeed.expr (k:=k) code T lut).labels+0
    rw [Term.labels_eq,TickLUTSeed.expr_binds]
    simp [binds,t]
  · exact safe
  · exact fit
  · exact header
  · exact away
  · exact rows

end ThreeFlat.RAM.TickPaddedROM

end OAI
