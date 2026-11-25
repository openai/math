import OAI.Hierarchy.TaggedShorterGroups
import OAI.ThreeFlat.RAM.EffectSeedProcedure
import OAI.ThreeFlat.RAM.PhysicalExactRun
import Mathlib.Tactic.FinCases
import OAI.ThreeFlat.RAM.EffectLocation
import OAI.Hierarchy.TaggedShorterCheapCPU

namespace OAI
/-! # Sparse publication of the two endpoint masks and the common lane identifier -/

noncomputable section
namespace Hierarchy.TaggedShorterScatter
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat Routing CallPool RAM RAM.PhysicalProcedure
open TaggedShorterGroups
open scoped Classical Fin.CommRing BigOperators

variable {G : Type} [Fintype G] {D B M n W : ℕ}

abbrev Slot (C D : ℕ) := (Fin C × Bool) × Fin D

/-- Each candidate has one occupancy word. Each slot has a mask word and a packed identifier. -/
abbrev Field (C D : ℕ) := Fin C ⊕ (Bool × Slot C D)

def fieldIndex (C D : ℕ) : Field C D ≃ Fin (C+2*(C*2*D)) :=
  let sb : Fin C × Bool ≃ Fin (C*2) :=
    ((Equiv.refl _).prodCongr finTwoEquiv.symm).trans finProdFinEquiv
  let cell : Slot C D ≃ Fin (C*2*D) :=
    (sb.prodCongr (Equiv.refl _)).trans finProdFinEquiv
  let lane := (finTwoEquiv.symm.prodCongr cell).trans finProdFinEquiv
  (Equiv.sumCongr (Equiv.refl _) lane).trans finSumFinEquiv

/-- The address table depends only on the installed candidate and the public dimensions. -/
def layout (C D base : ℕ) (fit : base+(C+2*(C*2*D))≤2^W) : Field C D ↪ Word W where
  toFun f := ⟨base+(fieldIndex C D f).val, by have := (fieldIndex C D f).isLt; omega⟩
  inj' := by
    intro f h eqn
    apply (fieldIndex C D).injective
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val eqn)

variable (c : G → ℕ) (bound : ∀g, c g ≤ D) (hb : 0<B) (hw : B≤2^n)
variable (place : ∀g,Bool → Fin (c g) ↪ Fin D)

abbrev Occurrence (c : G → ℕ) := (g : G) × Fin (c g)

def candidate (u : Occurrence c) : Fin (capacity G D B M) :=
  groupBoard c bound B M (batchIndex hb u.1 u.2)

def slot (u : Occurrence c) (b : Bool) : Slot (capacity G D B M) D :=
  ((candidate c bound hb u,b),place u.1 b u.2)

def fields (u : Occurrence c) : List (Field (capacity G D B M) D × ℕ) :=
  [(.inl (candidate c bound hb u), 1),
   (.inr (false,slot c bound hb place u false),1),
   (.inr (true,slot c bound hb place u false),u.2.val%B),
   (.inr (false,slot c bound hb place u true),1),
   (.inr (true,slot c bound hb place u true),u.2.val%B)]

def contents : Field (capacity G D B M) D → ℕ
  | .inl i => (groupOccupied c bound B M i).toNat
  | .inr (false,sb,x) => (groupMask c bound B M place sb x).toNat
  | .inr (true,sb,x) => ((wordBits n).symm (groupID c bound M hb hw place sb x)).val

/-- A native Boolean occupies the least significant wire of its word. -/
theorem bool_low (b : Bool) (wide : 0<W) :
    wordBits W (b.toNat : Word W) ⟨0,wide⟩=b := by
  cases b with
  | false => exact wordBits_zero _
  | true =>
    change (finFunctionFinEquiv.symm (1 : Word W) ⟨0,wide⟩ == 1)=true
    rw [beq_iff_eq,Fin.ext_iff,finFunctionFinEquiv_symm_apply_val]
    simp [Nat.mod_eq_of_lt (Nat.one_lt_two_pow wide.ne')]

/-- Both native flags need precisely one wire in the joined physical host. -/
theorem low_controls (addr : Field (capacity G D B M) D ↪ Word W) (m : Memory W)
    (wide : 0<W) (stored : ∀ f,m (addr f).val=(contents c bound hb hw place f : Word W)) :
    (∀ i,wordBits W (m (addr (.inl i)).val) ⟨0,wide⟩=groupOccupied c bound B M i) ∧
    (∀ sb x,wordBits W (m (addr (.inr (false,sb,x))).val) ⟨0,wide⟩=
      groupMask c bound B M place sb x) := by
  constructor
  · intro i
    rw [stored]
    exact bool_low _ wide
  · intro sb x
    rw [stored]
    exact bool_low _ wide

private def atUnit (u : Occurrence c) :
    AtCandidate (groupBoard c bound B M) (CallPool.Unit c B) (candidate c bound hb u) :=
  ⟨⟨batchIndex hb u.1 u.2,⟨u.2,rfl⟩⟩,rfl⟩

private theorem active (u : Occurrence c) (b : Bool) :
    contents (M:=M) c bound hb hw place (.inl (candidate (M:=M) c bound hb u))=1 ∧
    contents (M:=M) c bound hb hw place (.inr (false,slot (M:=M) c bound hb place u b))=1 ∧
    contents (M:=M) c bound hb hw place (.inr (true,slot (M:=M) c bound hb place u b))=u.2.val%B := by
  let z := atUnit (M:=M) c bound hb u
  let i := candidate (M:=M) c bound hb u
  have occ : Nonempty (AtCandidate (groupBoard c bound B M) (CallPool.Unit c B) i) := ⟨z⟩
  have landed : place u.1 b u.2 ∈ Set.range (groupAddress c bound B M place i b) := ⟨z,rfl⟩
  have idAt := active_groupID c bound M hb hw place i b z
  change groupID c bound M hb hw place (i,b) (place u.1 b u.2) =
    wordBits n ((offset hb z.val.1 z.val.2).castLE hw) at idAt
  refine ⟨by simpa [contents,groupOccupied,i] using
    (show (decide (Nonempty (AtCandidate (groupBoard c bound B M) (CallPool.Unit c B) i))).toNat=1 by simp [occ]),
    ?_,?_⟩
  · change (decide (place u.1 b u.2 ∈ Set.range (groupAddress c bound B M place i b))).toNat=1
    simp [landed]
  · change ((wordBits n).symm (groupID c bound M hb hw place (i,b) (place u.1 b u.2))).val=_
    rw [idAt,Equiv.symm_apply_apply]
    rfl

theorem fields_agree (u : Occurrence c) (p : Field (capacity G D B M) D × ℕ)
    (h : p∈fields c bound hb place u) : p.2 = contents c bound hb hw place p.1 := by
  have a := active (M:=M) c bound hb hw place u false
  have b := active (M:=M) c bound hb hw place u true
  simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl
  exacts [a.1.symm,a.2.1.symm,a.2.2.symm,b.2.1.symm,b.2.2.symm]

private theorem occurs {i : Fin (capacity G D B M)}
    (z : AtCandidate (groupBoard c bound B M) (CallPool.Unit c B) i) :
    candidate c bound hb (⟨z.val.1.1,z.val.2.val⟩ : Occurrence c) = i := by
  obtain ⟨⟨⟨g,k⟩,u⟩,eqn⟩ := z
  have which : batchIndex hb g u.val = (⟨g,k⟩ : Batch c B) := by
    have q : (batchIndex hb g u.val).2=k := Fin.ext u.property
    exact congrArg (Sigma.mk g) q
  simpa only [candidate,which] using eqn

theorem reaches (f : Field (capacity G D B M) D)
    (live : contents c bound hb hw place f ≠ 0) :
    ∃ u : Occurrence c, ∃ p ∈ fields c bound hb place u, p.1=f := by
  rcases f with i|⟨tag,sb,x⟩
  · have nz : Nonempty (AtCandidate (groupBoard c bound B M) (CallPool.Unit c B) i) := by
      by_contra empty
      simp [contents,groupOccupied,empty] at live
    obtain ⟨z⟩ := nz
    let u : Occurrence c := ⟨z.val.1.1,z.val.2.val⟩
    exact ⟨u,_,List.Mem.head _,congrArg Sum.inl (occurs c bound hb z)⟩
  · obtain ⟨i,b⟩ := sb
    have image : x∈Set.range (groupAddress c bound B M place i b) := by
      by_contra outside
      have blank := Function.extend_apply'
        (locatedAddress (groupBoard c bound B M) (localID hb hw) i)
        (fun _ : Fin D => fun _ : Fin n => false) x outside
      have empty : (wordBits n).symm (fun _ => false)=0 := by
        apply (wordBits n).injective
        rw [Equiv.apply_symm_apply]
        funext j
        exact (wordBits_zero j).symm
      cases tag <;> simp [contents,groupMask,groupID,outside,blank,empty] at live
    obtain ⟨z,rfl⟩ := image
    let u : Occurrence c := ⟨z.val.1.1,z.val.2.val⟩
    have addr : slot c bound hb place u b = ((i,b),groupAddress c bound B M place i b z) := by
      unfold slot
      rw [occurs c bound hb z]
      rfl
    refine ⟨u,(.inr (tag,slot c bound hb place u b), if tag then u.2.val%B else 1),?_,?_⟩
    · cases tag <;> cases b <;> simp [fields]
    · exact congrArg (fun s => Sum.inr (tag,s)) addr

theorem contents_fit (f : Field (capacity G D B M) D) (one : 1<2^W) (fits : B≤2^W) :
    contents c bound hb hw place f<2^W := by
  by_cases zero : contents c bound hb hw place f=0
  · rw [zero]
    exact Nat.two_pow_pos _
  · obtain ⟨u,p,mem,eqn⟩ := reaches c bound hb hw place f zero
    rw [←eqn,←fields_agree c bound hb hw place u p mem]
    have room := (Nat.mod_lt u.2.val hb).trans_le fits
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl <;> first | exact one | exact room

/-- Ordinary RAM word reads recover every bit including blank mask/ID words,
without a one-word truth-table assumption on any dynamic board field. -/
theorem decode_words (addr : Field (capacity G D B M) D ↪ Word W) (m : Memory W)
    (one : 1<2^W) (fits : B≤2^W)
    (stored : ∀f,m (addr f).val=(contents c bound hb hw place f:Word W)) :
    (∀ i,decide ((m (addr (.inl i)).val).val≠0)=groupOccupied c bound B M i) ∧
    (∀ sb x,decide ((m (addr (.inr (false,sb,x))).val).val≠0)=
      groupMask c bound B M place sb x) ∧
    (∀ sb x,wordBits n (((m (addr (.inr (true,sb,x))).val).val:ℕ):Word n)=
      groupID c bound M hb hw place sb x) := by
  have read f : (m (addr f).val).val=contents c bound hb hw place f := by
    rw [stored,Fin.val_cast_of_lt (contents_fit c bound hb hw place f one fits)]
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [read]
    change decide ((groupOccupied c bound B M i).toNat≠0)=_
    cases groupOccupied c bound B M i <;> rfl
  · intro sb x
    rw [read]
    change decide ((groupMask c bound B M place sb x).toNat≠0)=_
    cases groupMask c bound B M place sb x <;> rfl
  · intro sb x
    rw [read]
    change wordBits n (((wordBits n).symm (groupID c bound M hb hw place sb x)).val:Word n)=_
    simp

/-- Five sparse writes are issued for each live transport unit in its original enumeration. -/
def records (address : Field (capacity G D B M) D ↪ Word W) (order : List (Occurrence c)) :
    List (EffectStream.Record W) :=
  (order.flatMap (fields (M:=M) c bound hb place)).map (fun p => (address p.1,(p.2 : Word W)))

@[simp] theorem records_length (addr : Field (capacity G D B M) D ↪ Word W) (order : List (Occurrence c)) :
    (records c bound hb place addr order).length = 5*order.length := by
  induction order with
  | nil => simp [records]
  | cons u rest ih =>
    simp [records,fields,Nat.mul_succ] at ih ⊢
    omega

theorem scatter_reads (addr : Field (capacity G D B M) D ↪ Word W) (order : List (Occurrence c))
    (complete : ∀u,u∈order) (mem : Memory W) (cleared : ∀ f, mem (addr f).val=0)
    (f : Field (capacity G D B M) D) :
    after mem (EffectStream.events (records c bound hb place addr order)) (addr f).val =
      (contents c bound hb hw place f : Word W) := by
  apply EffectStream.after_at
  · intro x hx equal
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
    obtain ⟨u,_,hu⟩ := List.mem_flatMap.mp hp
    have eqn : p.1=f := addr.injective (Fin.ext equal)
    rw [←eqn]
    exact congrArg (fun a : ℕ => (a : Word W)) (fields_agree c bound hb hw place u p hu)
  · by_cases zero : contents c bound hb hw place f = 0
    · exact Or.inl (by simp [zero,cleared])
    · obtain ⟨u,p,hp,hf⟩ := reaches c bound hb hw place f zero
      exact Or.inr ⟨_,List.mem_map.mpr ⟨p,List.mem_flatMap.mpr ⟨u,complete u,hp⟩,rfl⟩,
        congrArg (fun t => (addr t).val) hf⟩

theorem scatter_exec (addr : Field (capacity G D B M) D ↪ Word W) (order : List (Occurrence c))
    (src : ℕ) (mem : Memory W)
    (loaded : EffectStream.Loaded mem src (records c bound hb place addr order))
    (room : src+2*(5*order.length)<2^W)
    (away : ∀ f, (addr f).val<src ∨ src+2*(5*order.length)≤(addr f).val) :
    (EffectSeed.scatter W src (5*order.length)).Exec mem
      (after mem (EffectStream.events (records c bound hb place addr order))) (4+30*order.length) := by
  let es := records c bound hb place addr order
  have len : es.length=5*order.length := records_length ..
  have safe : EffectStream.Safe src es := by
    intro av h
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp h
    simpa [len] using away p.1
  have run : (EffectSeed.scatter W src es.length).Exec mem (after mem (EffectStream.events es))
      (4+6*es.length) := Procedure.Spec.exec (EffectSeed.scatter_spec src es (by rwa [len]) safe) mem loaded
  rw [len,←Nat.mul_assoc] at run
  intro P R K M pc reg pub exit installed publicData cfg raw start eq
  exact run M pc reg pub exit installed publicData cfg raw start eq

theorem scatter_cheap (W src count : ℕ) {P R K : ℕ} (pc : Fin 9 ↪ Fin P)
    (reg : Fin 5 ↪ Fin R) (pub : Fin 2 → Fin K) (exit : Fin P) (i : Fin 9) :
    TaggedShorterCheapCPU.Cheap ((EffectSeed.scatter W src count).block.emit pc reg pub exit i) := by
  fin_cases i <;> trivial

end Hierarchy.TaggedShorterScatter

end
end OAI
