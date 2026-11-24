import OAI.Computability.VPVNP.PairTreeDecoder

/-! # Local role-reader contracts for exact traversal of a selected term tree -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open BurstRAM PrivateRAM DFS NetworkKernel CompressorRecords LocalHistory NodeArguments
open scoped Fin.CommRing

variable {W endAddr : ℕ} (hook : HookParser W endAddr)
    (valid : List Packet → Scratch W endAddr → Prop)
    {R : Type*} [CommRing R] {L : Type} [Fintype L] {f : L → R} {N : Network}

private theorem suffix_some {α β : Type*} {native : Option (β × List Bool)} (C : ChoiceReader α)
    {bits tail : List Bool} (same : native.map Prod.snd = (C.read bits).map Prod.snd) :
    (∃ j, native = some (j,tail)) ↔ ∃ x, bits = C.encode x ++ tail := by
  constructor
  · rintro ⟨j,read⟩
    rw [read,Option.map_some] at same
    obtain ⟨⟨x,rest⟩,hit,rfl⟩ := Option.map_eq_some_iff.mp same.symm
    exact ⟨x,(C.read_iff bits x rest).mp hit⟩
  · rintro ⟨x,hx⟩
    rw [(C.read_iff _ _ _).mpr hx,Option.map_some] at same
    obtain ⟨⟨j,rest⟩,hit,rfl⟩ := Option.map_eq_some_iff.mp same
    exact ⟨j,hit⟩

/-- This is the local part of the term's reader: first the independent
child half-wires, then that term's own checked kernel choices. -/
noncomputable def nodeReader {t : Term R N} (r : TermParsers f t) (v : t.output.Site) (z : t.output.Half v) :
    ChoiceReader ((a : Placed t.place N.Half v) × (r.witness v a z).Choice) :=
  (fiber t.place v (r.order.children v) (fun u => half N u (r.order.outgoing u) (r.order.incoming u) r.payload)).sigma
    (fun a => r.read v a z)

theorem nodeReader_encode {t : Term R N} (r : TermParsers f t) (v : t.output.Site) (z : t.output.Half v)
    (a : Placed t.place N.Half v) (k : (r.witness v a z).Choice) :
    (nodeReader r v z).encode ⟨a,k⟩ = r.nodeBits v a z k := rfl

/-- Suffix equality and the effect of the native writes suffice for both
directions of the term-row contract. The write effect is required only for
the exact placed assignment and local kernel occurrence read by that row. -/
theorem nodeStep_of_suffix {t : Term R N} (r : TermParsers f t) (ptr : t.output.Site → ℕ × ℕ)
    (before : Packets N) (next : Packets t.output)
    (suffix : ∀ v z pending s bits, valid (next v z::pending) s →
      (hook.read ((ptr v).1 : Word W) s bits).map Prod.snd = ((nodeReader r v z).read bits).map Prod.snd)
    (write : ∀ v z pending s bits job tail a k, valid (next v z::pending) s →
      hook.read ((ptr v).1 : Word W) s bits = some (job,tail) → bits = r.nodeBits v a z k ++ tail →
      valid (children r before v a ++ pending) (job.update s)) :
    NodeStep hook valid r ptr before next := by
  constructor
  · intro v z pending s bits job tail ready hit
    obtain ⟨⟨a,k⟩,eqn⟩ := (suffix_some (nodeReader r v z) (suffix v z pending s bits ready)).mp ⟨job,hit⟩
    exact ⟨a,k,eqn,write v z pending s bits job tail a k ready hit eqn⟩
  · intro v z pending s a k tail ready
    let bits := r.nodeBits v a z k ++ tail
    obtain ⟨job,hit⟩ := (suffix_some (nodeReader r v z) (suffix v z pending s bits ready)).mpr ⟨⟨a,k⟩,rfl⟩
    exact ⟨job,hit,write v z pending s bits job tail a k ready hit rfl⟩

/-- With the state parser's actual half-wire order the child packet list is
literally the one built by the selected term's native argument pass. -/
theorem children_childPackets {t : Term R N} (r : TermParsers f t) (addr : N.Site → ℕ)
    (v : t.output.Site) (a : Placed t.place N.Half v) :
    children r (fun u z => ⟨addr u, r.halfBits u z⟩) v a = r.childPackets addr v a := rfl

/-- The physical leaf's suffix equality with its cursor reader and its
preservation of the pending packets give the initial subtree induction. -/
theorem leaf_subtrees (P : SiteParsers f N) (ptr : N.Site → ℕ × ℕ) (pack : Packets N)
    (suffix : ∀ v z pending s bits, valid (pack v z::pending) s →
      (hook.read ((ptr v).1 : Word W) s bits).map Prod.snd = ((P.read v z).read bits).map Prod.snd)
    (frame : ∀ v z pending s bits job tail, valid (pack v z::pending) s →
      hook.read ((ptr v).1 : Word W) s bits = some (job,tail) → valid pending (job.update s)) :
    Subtrees hook valid P (fun v => leafTree (ptr v)) pack := by
  intro v z
  have order : ((leafTree (ptr v)).preorder.map (fun n : ℕ => (n : Word W))) = [((ptr v).1 : Word W)] := rfl
  constructor
  · intro pending s bits out tail ready run
    rw [order,HookParser.decode] at run
    obtain ⟨⟨job,rest⟩,hit,done⟩ := Option.bind_eq_some_iff.mp run
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj done : (job.update s,rest) = (out,tail)).symm
    exact ⟨(suffix_some (P.read v z) (suffix v z pending s bits ready)).mp ⟨job,hit⟩,
      frame v z pending s bits job _ ready hit⟩
  · intro pending s x tail ready
    let bits := (P.read v z).encode x ++ tail
    obtain ⟨job,hit⟩ := (suffix_some (P.read v z) (suffix v z pending s bits ready)).mpr ⟨x,rfl⟩
    refine ⟨job.update s,?_⟩
    rw [order,HookParser.decode]
    exact Option.bind_eq_some_iff.mpr ⟨(job,tail),hit,rfl⟩

/-- The selected occurrence is unique for any exact native suffix, including
the empty suffix used by the actual burst return. -/
theorem ExactBlock.unique {α : Type*} {args nodes} (C : ChoiceReader α)
    (h : ExactBlock hook valid args nodes C.encode) {pending s} (prepared : valid (args++pending) s)
    (bits tail : List Bool) :
    (∃ out, hook.decode nodes s bits = some (out,tail)) ↔ ∃! x, bits = C.encode x ++ tail := by
  rw [h.iff hook valid prepared]
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨x,hx,?_⟩
    intro y hy
    exact congrArg Prod.fst (Option.some.inj (((C.read_iff bits y tail).mpr hy).symm.trans
      ((C.read_iff bits x tail).mpr hx)))
  · rintro ⟨x,hx,_⟩; exact ⟨x,hx⟩

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
