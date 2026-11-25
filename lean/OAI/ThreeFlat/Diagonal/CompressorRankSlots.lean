import OAI.ThreeFlat.Diagonal.CompressorRankCorrect
import OAI.ThreeFlat.Diagonal.CompressorRegularize

namespace OAI
/-! # Native rank and lookup reproduce the regular graph's slot numbering -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Rank
open Computability.VPVNP.BurstRAM CompressorRegularize
open scoped Fin.NatCast
variable {w d : ℕ} {E B : Type*} [Fintype E] [LinearOrder E] [DecidableEq B]

theorem lookup_local (f : E → B) (uniform : ∀ b, (incident f b).card = d)
    (key : E ↪o Word w) (list : B → List (Word w))
    (complete : ∀ b, eligible (list b) = (incident f b).map key.toEmbedding)
    (fit : d ≤ 2^w) (b : B) (i : Fin d) :
    chosen (list b) (i.val : Word w) (list b) = key ((numbering f uniform).symm (b,i)) := by
  let s := incident f b
  have n : (eligible (list b)).card=d := by rw [complete,Finset.card_map,uniform]
  let g := fun j : Fin d => key (s.orderEmbOfFin (uniform b) j)
  have mem (j : Fin d) : g j ∈ eligible (list b) := by
    rw [complete]
    exact Finset.mem_map.mpr ⟨_,s.orderEmbOfFin_mem _ _,rfl⟩
  have mono : StrictMono g := key.strictMono.comp (s.orderEmbOfFin (uniform b)).strictMono
  have eq := Finset.orderEmbOfFin_unique n mem mono
  rw [chosen_index _ n fit]
  change (eligible (list b)).orderEmbOfFin n i = g i
  exact (congrFun eq i).symm

theorem rank_local (f : E → B) (uniform : ∀ b, (incident f b).card = d)
    (key : E ↪o Word w) (list : B → List (Word w))
    (complete : ∀ b, eligible (list b) = (incident f b).map key.toEmbedding)
    (e : E) : (below (list (f e)) (key e)).card = (numbering f uniform e).2.val := by
  let b := f e
  let s := incident f b
  let i := (numbering f uniform e).2
  have n : (eligible (list b)).card = d := by rw [complete,Finset.card_map,uniform]
  let g := fun j : Fin d => key (s.orderEmbOfFin (uniform b) j)
  have mem (j : Fin d) : g j ∈ eligible (list b) := by
    rw [complete]
    exact Finset.mem_map.mpr ⟨_,s.orderEmbOfFin_mem _ _,rfl⟩
  have eq := Finset.orderEmbOfFin_unique n mem
    (key.strictMono.comp (s.orderEmbOfFin (uniform b)).strictMono)
  have inv : (numbering f uniform).symm (b,i) = e :=
    (numbering f uniform).symm_apply_apply e
  have ord : ((eligible (list b)).orderIsoOfFin n i).val = key e := by
    exact (congrFun eq i).symm.trans (congrArg key inv)
  rw [show f e = b from rfl,← ord,eligible_below,below_index]

end ThreeFlat.Diagonal.CompressorPacking.Native.Rank

end OAI
