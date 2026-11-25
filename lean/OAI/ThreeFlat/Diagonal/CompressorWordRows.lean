import OAI.ThreeFlat.Diagonal.CompressorDemandROM
import OAI.ThreeFlat.Diagonal.CompressorCandidateImage
import OAI.ThreeFlat.Diagonal.CompressorOpsMap
import OAI.ThreeFlat.Diagonal.CompressorTemplateEmit

namespace OAI
/-! # The same local candidate traversal in syntax, memory words and physical motifs -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.Graph
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Placement
open scoped Classical Fin.NatCast

def allAt {A : Type*} (o : Ops A) (g : ArcColumns A) (r : Radices A) (S : Stage)
    (lay rev : Bool) (b : Site A) : List (Candidate A) :=
  (List.finRange 4).flatMap fun k =>
    (List.finRange (S.pieces k)).flatMap fun j =>
      [false,true].flatMap fun thin =>
        (List.finRange S.degree).flatMap fun h =>
          (List.finRange (2^S.colors)).flatMap fun u =>
            [false,true].flatMap fun inc =>
              (List.finRange S.degree).map fun i => candidateWith o g r S lay rev thin inc b k j h u i

def allWords {A : Type*} (o : Ops A) (g : ArcColumns A) (r : Radices A) (S : Stage)
    (lay rev : Bool) (base : A) : List (Candidate A) :=
  allAt o g r S lay rev ⟨o.bin .div base r.tags,o.bin .mod base r.tags,o.lit 0⟩

theorem map_allAt {A B : Type*} {o : Ops A} {p : Ops B} {f : A → B} (H : OpMap o p f)
    (g : ArcColumns A) (r : Radices A) (S : Stage) (lay rev : Bool) (b : Site A) :
    (allAt o g r S lay rev b).map (Candidate.map f) =
      allAt p (g.map f) (r.map f) S lay rev (b.map f) := by
  simp [allAt,List.map_flatMap,List.map_map,Function.comp_def,H.candidate]

theorem map_allWords {A B : Type*} {o : Ops A} {p : Ops B} {f : A → B} (H : OpMap o p f)
    (g : ArcColumns A) (r : Radices A) (S : Stage) (lay rev : Bool) (base : A) :
    (allWords o g r S lay rev base).map (Candidate.map f) =
      allWords p (g.map f) (r.map f) S lay rev (f base) := by
  simp only [allWords,map_allAt H,Site.map,H.bin,H.lit,Radices.map]

variable {w k n : ℕ}
theorem term_candidates (g : ArcColumns (T w k n)) (r : Radices (T w k n)) (S : Stage)
    (lay rev : Bool) (v : T w k n) : candidates g r S lay rev v = allWords (terms w k n) g r S lay rev v := rfl

theorem template_candidates (S : Stage) (lay rev : Bool) (v : ShrinkStage.Template.F) :
    ShrinkStage.Template.candidates S lay rev v =
    allWords ShrinkStage.Template.o ShrinkStage.Template.g (ShrinkStage.radices ShrinkStage.Template.o
      ShrinkStage.Template.ptr S) S lay rev v := rfl

variable {B : Type*} {t l : ℕ}
theorem word_site (S : Stage) (E : Codec B w S.colors t l) (m : Memory w) (v : B × BitWord t)
    (fit : (E.base v.1).val*2^t+(tagOrdinal t v.2).val < 2^w) (tags : 2^t<2^w) :
    (⟨(words m).bin .div (baseAddress S E v) (rowRadices (w:=w) (t:=t) (l:=l) S).tags,
      (words m).bin .mod (baseAddress S E v) (rowRadices (w:=w) (t:=t) (l:=l) S).tags,
      (words m).lit 0⟩ : Site (Word w)) = siteCode E (v.1,v.2,(0:BitWord l)) := by
  let b := (E.base v.1).val
  let z := (tagOrdinal t v.2).val
  have old : baseAddress S E v = ((b*2^t+z:ℕ):Word w) := by
    have product : E.base v.1 * ((2^t : ℕ) : Word w) = ((b*2^t : ℕ) : Word w) := by
      apply Fin.ext
      change (b * (2^t % 2^w)) % 2^w = (b * 2^t) % 2^w
      rw [Nat.mod_eq_of_lt tags]
    simp only [baseAddress,Nat.cast_add,z,Demand.tag_cast E.tags v.2,product]
  have hd : (b*2^t+z)/2^t = b := by
    rw [Nat.mul_comm b (2^t),Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt (tagOrdinal t v.2).isLt,Nat.add_zero]
  have hm : (b*2^t+z)%2^t = z := by simp [Nat.add_mod,z,Nat.mod_eq_of_lt (tagOrdinal t v.2).isLt]
  simp only [words,old,rowRadices,RAM.PhysicalPinsExpr.op_cast .div _ _ ⟨fit,tags⟩,
    RAM.PhysicalPinsExpr.op_cast .mod _ _ ⟨fit,tags⟩,RAM.PhysicalPinsExpr.natOp,hd,hm,
    siteCode,b,z,Fin.cast_val_eq_self,Demand.tag_cast E.tags v.2,tagWord_zero,Nat.cast_zero]

theorem visit_rows (S : Stage) (E : Codec B w S.colors t l) (G : ArcColumns (Word w)) (m : Memory w)
    (lay rev : Bool) (v : B × BitWord t) (fit : (E.base v.1).val*2^t+(tagOrdinal t v.2).val<2^w)
    (tags : 2^t<2^w) :
    allWords (words m) G (rowRadices (w:=w) (t:=t) (l:=l) S) S lay rev (baseAddress S E v) =
      visitWords S E G m lay rev v := by
  rw [allWords,word_site S E m v fit tags]
  simp only [visitWords,visitWord,Local.visits,allAt,List.map_flatMap,List.map_map,Function.comp_def,
    Equiv.apply_symm_apply]


end ThreeFlat.Diagonal.CompressorPacking.Native.Graph

end OAI
