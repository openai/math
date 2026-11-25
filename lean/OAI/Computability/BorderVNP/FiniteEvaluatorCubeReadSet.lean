import OAI.Computability.BorderVNP.FiniteEvaluatorCubeDeck

/-! # Physical memory words needed by the field cube lookup

The dynamic reference addresses and limits are reconstructed from the live
triples and fixed recipes. The frame entries used by this lookup exclude
the count word written by the owned-cell task builder.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubePacket

open VPVNP.BurstRAM RoutingISA BorderVNP.Cube BorderVNP.Cube.Tally DiagonalTallyPacketEmit

variable {F : Type*} [Fintype F] {n b h K s w : ℕ}
variable (P : Inputs n b h K s F) {pub : Arg → Word w} {mem mt : Memory w}

/-- Indices of the primary words read by the reference and scalar programs. -/
def frameWords : List ℕ := [45,46,47,71,78,79,80,81,82,83,84]

/-- All address intervals needed by the complete cube lookup. -/
inductive ReadAt (P : Inputs n b h K s F) (pub : Arg → Word w) : ℕ → Prop
  | frame (j : ℕ) (needed : j ∈ frameWords) : ReadAt P pub ((pub 0).val+j)
  | zero : ReadAt P pub P.frame.zeroAddr
  | one : ReadAt P pub P.frame.oneAddr
  | recipe (j : ℕ) (bound : j < (CubeConstants.recipes n b h K s).length) : ReadAt P pub (P.frame.recipes+j)
  | value (j : ℕ) (bound : j < 2^argumentWidth n b h K s) : ReadAt P pub (P.table+j)
  | triple (j : ℕ) (bound : j < 3*P.frame.count) : ReadAt P pub (P.frame.triples+j)
  | bank (i : Fin P.frame.count) (j : ℕ) (bound : j < bankWidth n b h K s) : ReadAt P pub ((P.visits i).base+j)

omit [Fintype F] in
/-- Transport the dynamic lookups using the actual immutable frame, triple
words and packet banks, together with the fixed recipe and scalar tables. -/
theorem word_transfer_of_tables {id : TableEntry n b h K s → ℕ} (original : WordPrepared P id pub mem)
    (fields : ∀ j ∈ frameWords, mt ((pub 0).val+j)=mem ((pub 0).val+j))
    (records : ∀ j < 3*P.frame.count, mt (P.frame.triples+j)=mem (P.frame.triples+j))
    (bank : ∀ i, ∀ j < bankWidth n b h K s, mt ((P.visits i).base+j)=mem ((P.visits i).base+j))
    (recipes : P.frame.recipeAt (readings mt) n b h K s)
    (zero : (mt P.frame.zeroAddr).val=0) (one : (mt P.frame.oneAddr).val=1)
    (deck : ∀ k < 2^argumentWidth n b h K s, (mt (P.table+k)).val =
      idTable (selectorOrder n K h) (vertexOrder _) id k) : WordPrepared P id pub mt := by
  have field (j : ℕ) (hj : j ∈ frameWords) := congrArg Fin.val (fields j hj)
  have orig := original.frame
  dsimp only [Frame.resident,readings] at orig
  obtain ⟨ct,tr,rec,refs,desc,lit0,lit1,wd,vs⟩ := orig
  have frame' : P.frame.resident (readings pub) (readings mt) :=
    ⟨(field 46 (by decide)).trans ct,(field 78 (by decide)).trans tr,(field 79 (by decide)).trans rec,
      (field 80 (by decide)).trans refs,(field 45 (by decide)).trans desc,(field 81 (by decide)).trans lit0,
      (field 82 (by decide)).trans lit1,(field 83 (by decide)).trans wd,(field 84 (by decide)).trans vs⟩
  have triple (i : Fin P.frame.count) (j : ℕ) (hj : j<3) :
      readings mt (P.frame.triples+3*i.val+j)=readings mem (P.frame.triples+3*i.val+j) := by
    rw [Nat.add_assoc]
    exact congrArg Fin.val (records _ (by have := i.isLt; omega))
  have triples (i : Fin P.frame.count) : (P.visits i).tripleAt (readings mt) (P.frame.triples+3*i.val) := by
    obtain ⟨a,b,c⟩ := original.triples i
    exact ⟨(triple i 0 (by decide)).trans a,(triple i 1 (by decide)).trans b,(triple i 2 (by decide)).trans c⟩
  have banks (i : Fin P.frame.count) :
      VertexAt mt (P.visits i).base (P.visits i).selector (P.visits i).vertex (P.visits i).ends (P.visits i).supply := by
    have keep (j : ℕ) (hj : j < bankWidth n b h K s) :=
      congrArg Fin.val (bank i j hj)
    have lower : selectorWidth n K h ≤ bankWidth n b h K s := by unfold bankWidth supplyBase; omega
    refine ⟨fun j => (keep j.val (j.isLt.trans_le lower)).trans ((original.banks i).selector j),
      fun e attached j => (keep _ ((demandOffset_range e j).2.trans_le (Nat.le_add_right _ _))).trans ((original.banks i).demand e attached j),
      fun e incident j => (keep _ (supplyOffset_range (P.visits i).selector e j).2).trans ((original.banks i).supply e incident j)⟩
  have fit := original.fits
  have fit' : Frame.Fits P.frame (readings mt) w (pub 0).val := by
    refine ⟨fit.frameBefore,fit.triplesBefore,?_,fit.outputs,fit.room,?_,?_⟩
    · intro i hi j hj
      have a := triple ⟨i,hi⟩ 1 (by decide)
      have b := triple ⟨i,hi⟩ 2 (by decide)
      simpa only [Frame.recipeAddr,a,b] using fit.recipesBefore i hi j hj
    · intro k hk
      have positive : 0<P.frame.width := by by_contra! h; have := Nat.eq_zero_of_le_zero h; simp_all
      have i : k/P.frame.width < P.frame.count := (Nat.div_lt_iff_lt_mul positive).mpr hk
      have j := Nat.mod_lt k positive
      have split : k/P.frame.width * P.frame.width + k%P.frame.width=k := by rw [Nat.mul_comm]; exact Nat.div_add_mod ..
      let t : Fin P.frame.count := ⟨k/P.frame.width,i⟩
      have old := (P.visits t).generatedRef P.frame (readings mem) t.val original.recipe (original.triples t) j
      have new := (P.visits t).generatedRef P.frame (readings mt) t.val recipes (triples t) j
      have eq := new.trans old.symm
      change P.frame.refValue (readings mt) (k/P.frame.width*P.frame.width+k%P.frame.width) =
        P.frame.refValue (readings mem) (k/P.frame.width*P.frame.width+k%P.frame.width) at eq
      rw [split] at eq
      exact eq ▸ fit.digit k hk
    · intro i hi
      have a := triple ⟨i,hi⟩ 1 (by decide)
      have b := triple ⟨i,hi⟩ 2 (by decide)
      simpa only [a,b] using fit.slice i hi
  exact ⟨frame',fit',recipes,triples,banks,zero,one,original.below,
    (field 47 (by decide)).trans original.tableWord,(field 71 (by decide)).trans original.dstWord,
    deck,original.tableFit,original.separate,original.room⟩

/-- The same physical relocation with the finite scalar deck's framed one-hot entries. -/
theorem transfer_of_tables (original : Prepared P pub mem)
    (fields : ∀ j ∈ frameWords, mt ((pub 0).val+j)=mem ((pub 0).val+j))
    (records : ∀ j < 3*P.frame.count, mt (P.frame.triples+j)=mem (P.frame.triples+j))
    (bank : ∀ i, ∀ j < bankWidth n b h K s, mt ((P.visits i).base+j)=mem ((P.visits i).base+j))
    (recipes : P.frame.recipeAt (readings mt) n b h K s)
    (zero : (mt P.frame.zeroAddr).val=0) (one : (mt P.frame.oneAddr).val=1)
    (deck : ∀ k < 2^argumentWidth n b h K s, (mt (P.table+k)).val =
      idTable (selectorOrder n K h) (vertexOrder _) (fun e => CubeWord.encode (P.entry e)) k) : Prepared P pub mt :=
  word_transfer_of_tables P original fields records bank recipes zero one deck

omit [Fintype F] in
/-- Complete cube operands transfer across any native stage preserving their actual words. -/
theorem WordPrepared.transfer {id : TableEntry n b h K s → ℕ} (original : WordPrepared P id pub mem)
    (same : ∀ a, ReadAt P pub a → mt a=mem a) : WordPrepared P id pub mt := by
  apply word_transfer_of_tables P original (fun j h => same _ (.frame j h)) (fun j h => same _ (.triple j h))
    (fun i j h => same _ (.bank i j h))
  · obtain ⟨width,vertices,read⟩ := original.recipe
    refine ⟨width,vertices,fun u v j hj => ?_⟩
    let i : Fin (argumentWidth n b h K s) := ⟨j,(recipe_length u v b s) ▸ hj⟩
    have small : (CubeConstants.recipeIndex u v i).val < (CubeConstants.recipes n b h K s).length := by
      simpa only [CubeConstants.recipes,List.length_ofFn] using (CubeConstants.recipeIndex u v i).isLt
    have keep := congrArg Fin.val (same _ (.recipe _ small))
    have atWord := read u v j hj
    rw [vertices,width,Nat.add_assoc P.frame.recipes _ j] at atWord ⊢
    rw [CubeConstants.recipeIndex_val] at keep
    exact keep.trans atWord
  · exact (congrArg Fin.val (same _ .zero)).trans original.zero
  · exact (congrArg Fin.val (same _ .one)).trans original.one
  · exact fun k hk => (congrArg Fin.val (same _ (.value _ hk))).trans (original.deck k hk)


/-- Complete framed finite-field operands survive stages preserving their live words. -/
theorem Prepared.transfer (original : Prepared P pub mem) (same : ∀ a, ReadAt P pub a → mt a=mem a) :
    Prepared P pub mt := WordPrepared.transfer P original same

end FiniteEvaluator.CubePacket

end BorderVNP
end Computability
end OAI
