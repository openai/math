import OAI.ThreeFlat.RAM.CachedBlock

namespace OAI
/-! # Operand relocation of linked public-word blocks -/

namespace ThreeFlat.RAM.CachedBlock
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink

variable {w n m r k P R K P' R' K' : ℕ}

theorem Natural.map_emit {b : Block w n r k} (hb : Natural b)
    (pc' : Fin n ↪ Fin P') (reg' : Fin r ↪ Fin R') (pub' : Fin k → Fin K') (exit' : Fin P')
    (pc : Fin n ↪ Fin P) (reg : Fin r ↪ Fin R) (pub : Fin k → Fin K) (exit : Fin P)
    (f : Fin P' → Fin P) (g : Fin R' → Fin R) (h : Fin K' → Fin K)
    (pco : ∀ j,f (pc' j)=pc j) (rgo : ∀ j,g (reg' j)=reg j) (puo : ∀ j,h (pub' j)=pub j)
    (eo : f exit'=exit) (i : Fin n) :
    b.emit pc reg pub exit i=mapInstr f g h (b.emit pc' reg' pub' exit' i) := by
  rw [hb pc reg pub exit i,hb pc' reg' pub' exit' i,mapInstr_comp]
  have hc : f ∘ targets pc' exit'=targets pc exit := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro l
      simpa only [Function.comp_apply,targets,Fin.addCases_left] using pco l
    · intro l
      simpa only [Function.comp_apply,targets,Fin.addCases_right] using eo
  rw [hc,show g ∘ reg'=reg from funext rgo,show h ∘ pub'=pub from funext puo]

theorem Natural.reindex {b : Block w n r k} {S L : ℕ} (hb : Natural b)
    (frame : Fin r ↪ Fin S) (params : Fin k → Fin L) : Natural (b.reindex frame params) := by
  intro P R K pc reg pub exit i
  change b.emit pc (frame.trans reg) (pub ∘ params) exit i =
    mapInstr (targets pc exit) reg pub (b.emit (Fin.castAddEmb 1)
      (frame.trans (Function.Embedding.refl _)) (id ∘ params) (Fin.natAdd n 0) i)
  apply hb.map_emit
  · intro j
    exact Fin.addCases_left ..
  · intro j
    rfl
  · intro j
    rfl
  · exact Fin.addCases_right ..

theorem Natural.seq {a : Block w n r k} {b : Block w m r k} (ha : Natural a) (hb : Natural b) :
    Natural (a.seq b) := by
  intro P R K pc reg pub exit i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [canonicalRow,Block.seq,Fin.addCases_left]
    apply ha.map_emit
    · intro t
      exact Fin.addCases_left ..
    · intro t
      rfl
    · intro t
      rfl
    · exact Fin.addCases_left ..
  · intro j
    simp only [canonicalRow,Block.seq,Fin.addCases_right]
    apply hb.map_emit
    · intro t
      exact Fin.addCases_left ..
    · intro t
      rfl
    · intro t
      rfl
    · exact Fin.addCases_right ..

end ThreeFlat.RAM.CachedBlock

end OAI
