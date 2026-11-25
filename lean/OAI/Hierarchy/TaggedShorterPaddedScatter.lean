import OAI.Hierarchy.TaggedShorterScatter

namespace OAI
/-! # Fixed-length publication over all potential transport positions -/

noncomputable section
namespace Hierarchy.TaggedShorterScatter
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat RAM RAM.PhysicalProcedure
open TaggedShorterGroups
open scoped Classical Fin.CommRing

variable {G : Type} [Fintype G] {D B M n W R : ℕ}
variable (c : G → ℕ) (bound : ∀g,c g≤D) (hb : 0<B)
variable (place : ∀g,Bool → Fin (c g) ↪ Fin D)
variable (addr : Field (capacity G D B M) D ↪ Word W) (sink : Word W)

def liveField (u : Occurrence c) (j : Fin 5) : Field (capacity G D B M) D × ℕ :=
  (fields c bound hb place u).get j

def paddedRecord (select : Fin R → Option (Occurrence c)) (p : Fin (R*5)) : EffectStream.Record W :=
  let (i,j) := finProdFinEquiv.symm p
  match select i with
  | none => (sink,0)
  | some u =>
    let v := liveField (M:=M) c bound hb place u j
    (addr v.1,(v.2 : Word W))

def paddedTape (select : Fin R → Option (Occurrence c)) :=
  List.ofFn (paddedRecord c bound hb place addr sink select)

theorem padded_reads (hw : B≤2^n) (select : Fin R → Option (Occurrence c))
    (covers : ∀u, ∃i,select i=some u) (outside : ∀f, sink≠addr f)
    (m : Memory W) (clear : ∀f,m (addr f).val=0)
    (f : Field (capacity G D B M) D) :
    after m (EffectStream.events (paddedTape c bound hb place addr sink select)) (addr f).val =
      (contents c bound hb hw place f : Word W) := by
  apply EffectStream.after_at
  · intro x hx same
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective k
    cases h : select i with
    | none =>
      have eqn : sink.val=(addr f).val := by simpa [paddedRecord,h] using same
      exact (outside f (Fin.ext eqn)).elim
    | some u =>
      let v := liveField (M:=M) c bound hb place u j
      have eqn : addr v.1=addr f := Fin.ext (by simpa [paddedRecord,h,v] using same)
      have val := fields_agree c bound hb hw place u v (List.get_mem ..)
      simpa [paddedRecord,h,v,addr.injective eqn] using
        congrArg (fun a : ℕ => (a : Word W)) (val.trans (congrArg _ (addr.injective eqn)))
  · by_cases zero : contents c bound hb hw place f=0
    · exact Or.inl (by simp [clear,zero])
    · obtain ⟨u,v,hv,atF⟩ := reaches c bound hb hw place f zero
      obtain ⟨i,hi⟩ := covers u
      obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hv
      let j' : Fin 5 := ⟨j.val,j.isLt⟩
      let k : Fin (R*5) := finProdFinEquiv (i,j')
      refine Or.inr ⟨_,List.mem_ofFn.mpr ⟨k,rfl⟩,?_⟩
      simp only [paddedRecord,k,Equiv.symm_apply_apply,hi,liveField]
      exact congrArg (fun x => (addr x).val) atF

theorem padded_exec (select : Fin R → Option (Occurrence c)) (src : ℕ) (m : Memory W)
    (loaded : EffectStream.Loaded m src (paddedTape c bound hb place addr sink select))
    (room : src+2*(R*5)<2^W)
    (away : ∀f, (addr f).val<src ∨ src+2*(R*5)≤(addr f).val)
    (safeSink : sink.val<src ∨ src+2*(R*5)≤ sink.val) :
    (EffectSeed.scatter W src (R*5)).Exec m
      (after m (EffectStream.events (paddedTape c bound hb place addr sink select))) (4+6*(R*5)) := by
  let es := paddedTape c bound hb place addr sink select
  have ln : es.length=R*5 := List.length_ofFn
  have safe : EffectStream.Safe src es := by
    intro av h
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp h
    obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective k
    rw [ln]
    cases hi : select i with
    | none => simpa [paddedRecord,hi] using safeSink
    | some u => simpa [paddedRecord,hi] using away (liveField c bound hb place u j).1
  have run : (EffectSeed.scatter W src es.length).Exec m (after m (EffectStream.events es))
      (4+6*es.length) := Procedure.Spec.exec (EffectSeed.scatter_spec src es (by rwa [ln]) safe) m loaded
  rw [ln] at run
  intro P X K machine pc reg pub exit installed publicData cfg raw start eq
  exact run machine pc reg pub exit installed publicData cfg raw start eq

end Hierarchy.TaggedShorterScatter

end
end OAI
