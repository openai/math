import OAI.Computability.VPVNP.PairShrinkRoleChild

/-!
# Recovering the old half-wire assignment from the native child tape

The outgoing slot order and the inverse incoming slot order reconstruct both
independent halves of each child. The native reader therefore returns the
actual typed arguments of a supplied witness, and every complete decode in
placement order yields such an assignment.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments.ChildScan

open Compression LocalHistory NetworkKernel CompressorRecords
variable {a g : ℕ} (X : State a g)

/-- The inverse to recording independent outgoing and incoming slot fields. -/
noncomputable def Child.half (x : Child X) : X.network.Half x.site :=
  let unorder {f : X.network.Edge → X.network.Site} (ord : Order {e // x.site = f e})
      (values : (j : Fin ord.length) → X.network.Payload (ord.entries j).val) :=
    fun e h => Equiv.piCongrLeft (fun z : {e // x.site = f e} => X.network.Payload z.val)
      ord.entries values ⟨e,h⟩
  (unorder (outgoingOrder X x.site) (fun j => x.data (false,j)),
    unorder (incomingOrder X x.site) (fun j => x.data (true,j)))

theorem Child.ofHalf_half (x : Child X) : Child.ofHalf X x.site (x.half X) = x := by
  rcases x with ⟨u, d⟩
  unfold Child.ofHalf
  congr 1
  funext i
  rcases i with ⟨b,j⟩
  cases b <;> exact Equiv.piCongrLeft_apply_apply ..


theorem Child.payload_eq_packed (x : Child X) : x.payload X = packed X x.site (x.half X) := by
  simpa only [Child.ofHalf_half] using Child.payload_ofHalf X x.site (x.half X)

private theorem Child.eq_of_half {x : Child X} {v : X.network.Site} (h : x.site = v) :
    Child.ofHalf X v (h ▸ x.half X) = x := by
  subst v
  exact Child.ofHalf_half X x

/-- Every list decoded in the placement order comes from old half-wire values
at precisely the sites in the placement fiber. -/
theorem exists_placed {R : Type*} {t : Term R X.network} (v : t.output.Site)
    (ord : Order (t.Preimage v)) (xs : List (Child X))
    (order : xs.map Child.site = List.ofFn fun j => (ord.entries j).val) :
    ∃ h : Placed t.place X.network.Half v, children X v ord h = xs := by
  have len : xs.length = ord.length := by simpa using congrArg List.length order
  have bound (j : Fin ord.length) : j.val < xs.length := len.symm ▸ j.isLt
  let atIndex (j : Fin ord.length) := xs[j.val]'(bound j)
  have site (j : Fin ord.length) : (atIndex j).site = (ord.entries j).val := by
    have h := congrArg (fun us => us[j.val]?) order
    simpa [atIndex, List.getElem?_eq_getElem (bound j), j.isLt] using h
  let halves (j : Fin ord.length) : X.network.Half (ord.entries j).val :=
    site j ▸ (atIndex j).half X
  let h : Placed t.place X.network.Half v := fun u hu =>
    Equiv.piCongrLeft (fun z : t.Preimage v => X.network.Half z.val) ord.entries halves ⟨u,hu⟩
  have selected (j : Fin ord.length) : h _ (ord.entries j).prop = halves j :=
    Equiv.piCongrLeft_apply_apply ..
  refine ⟨h, List.ext_getElem (by simp [children, len]) ?_⟩
  intro n hn hx
  let j : Fin ord.length := ⟨n, len ▸ hx⟩
  simp only [children, List.getElem_ofFn]
  exact (congrArg (Child.ofHalf X _) (selected j)).trans (Child.eq_of_half X (site j))

/-- A site's exact tape prefix determines its entire independent slot assignment
and the rest of the tape uniquely. -/
theorem Child.uniquePrefix {x y : Child X} (site : x.site = y.site) {s t : List Bool}
    (bits : x.payload X ++ s = y.payload X ++ t) : x = y ∧ s = t := by
  rcases x with ⟨u, xs⟩
  rcases y with ⟨v, ys⟩
  change u = v at site
  subst v
  let x : Child X := ⟨u,xs⟩
  let y : Child X := ⟨u,ys⟩
  let parser := LocalHistory.half X.network u (outgoingOrder X u) (incomingOrder X u)
    (statePayload X)
  have enc (z : Child X) : z.payload X = packed X z.site (z.half X) := z.payload_eq_packed X
  have words : parser.encode (x.half X) ++ s = parser.encode (y.half X) ++ t := by
    change x.payload X ++ s = y.payload X ++ t at bits
    rwa [enc x, enc y, packed_eq_encode, packed_eq_encode] at bits
  have one := (parser.read_iff _ (x.half X) s).mpr rfl
  have two := (parser.read_iff _ (y.half X) t).mpr words
  obtain ⟨equal, rest⟩ := Prod.mk.inj (Option.some.inj (one.symm.trans two))
  exact ⟨(x.ofHalf_half X).symm.trans
    ((congrArg (Child.ofHalf X u) equal).trans (y.ofHalf_half X)), rest⟩

theorem uniqueChildren {xs ys : List (Child X)} (order : xs.map Child.site = ys.map Child.site)
    {s t : List Bool}
    (bits : xs.flatMap (Child.payload X) ++ s = ys.flatMap (Child.payload X) ++ t) :
    xs = ys ∧ s = t := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at order
    | cons y ys =>
      obtain ⟨head, tail⟩ := List.cons.inj order
      rw [List.flatMap_cons, List.flatMap_cons, List.append_assoc, List.append_assoc] at bits
      obtain ⟨rfl, rem⟩ := Child.uniquePrefix X head bits
      obtain ⟨rfl, rfl⟩ := ih tail rem
      exact ⟨rfl, rfl⟩

end PairSimulation.NodeArguments.ChildScan

namespace PairSimulation.ShrinkRole.ChildArguments

open BurstRAM Compression CompressorRecords NodeArguments NodeArguments.ChildScan DFS

variable {a g w endAddr : ℕ} {X : State a g} (A : Arena) (T : IncidenceDirectory w)
  (m : Memory w) (older cap : ℕ) (desc : Word w → Descriptor w X)

/-- Feeding the encoded list of arbitrary typed children returns the very same
list, writes its packets, and leaves the supplied kernel suffix intact. -/
theorem reader_encoded (node : Word w) (saved : Scratch w endAddr) (xs : List (Child X))
    (sites : xs.map Child.site = (desc node).sites) (rest : List Bool) :
    reader A T m older cap desc node saved (xs.flatMap (Child.payload X) ++ rest) =
      some (outcome A T m older cap desc node saved xs, rest) := by
  let bs := xs.flatMap (Child.payload X) ++ rest
  have enough : demand X (desc node).sites ≤ bs.length := by
    rw [← sites, ← payload_length]
    simp [bs]
  let picked := chooseChildren X (desc node).sites bs enough
  obtain ⟨equal, suffix⟩ := uniqueChildren X (picked.choose_spec.1.trans sites.symm)
    picked.choose_spec.2
  change reader A T m older cap desc node saved bs = _
  simp only [reader, dite_eq_left enough]
  change some (outcome A T m older cap desc node saved picked.choose,
    bs.drop (demand X (desc node).sites)) = _
  rw [equal, suffix]

open NetworkKernel LocalHistory
open private fiber_encode from OAI.Computability.VPVNP.PairNodeArguments

variable {R : Type*} {t : Term R X.network} (v : t.output.Site) (ord : Order (t.Preimage v))

/-- The old half-wire part of the abstract site parser. -/
noncomputable def placedReader : ChoiceReader (Placed t.place X.network.Half v) :=
  fiber t.place v ord fun u =>
    LocalHistory.half X.network u (outgoingOrder X u) (incomingOrder X u) (statePayload X)

theorem children_bits (h : Placed t.place X.network.Half v) :
    (children X v ord h).flatMap (Child.payload X) = (placedReader v ord).encode h := by
  unfold placedReader
  rw [fiber_encode]
  simp only [children, List.flatMap_def, List.map_ofFn, Function.comp_def,
    Child.payload_ofHalf, packed_eq_encode]

private theorem children_injective : Function.Injective (children X v ord) := by
  intro x y equal
  let C := placedReader v ord
  have eqn : C.encode x = C.encode y := by
    rw [← children_bits v ord x, ← children_bits v ord y, equal]
  have one := (C.read_iff _ x []).mpr rfl
  have two := (C.read_iff _ y []).mpr (congrArg (· ++ []) eqn)
  exact (Prod.mk.inj (Option.some.inj (one.symm.trans two))).1

/-- Reading a placed half-wire witness consumes precisely its encoding and
returns the corresponding old children in the descriptor's order. -/
theorem reader_placed (node : Word w) (saved : Scratch w endAddr)
    (order : (desc node).sites = List.ofFn fun j => (ord.entries j).val)
    (h : Placed t.place X.network.Half v) (rest : List Bool) :
    reader A T m older cap desc node saved ((placedReader v ord).encode h ++ rest) =
      some (outcome A T m older cap desc node saved (children X v ord h), rest) := by
  rw [← children_bits]
  apply reader_encoded
  rw [order]
  simp [children, Child.ofHalf, Function.comp_def]

/-- The exact tape, old sites, slot values, and scratch returned by a complete
native read determine one placed half-wire assignment. -/
theorem reader_unique_placed (node : Word w) (saved : Scratch w endAddr)
    (order : (desc node).sites = List.ofFn fun j => (ord.entries j).val)
    {bs rest : List Bool} {out : Outcome w endAddr (List (Child X))}
    (read : reader A T m older cap desc node saved bs = some (out, rest)) :
    ∃! h : Placed t.place X.network.Half v,
      out = outcome A T m older cap desc node saved (children X v ord h) ∧
        bs = (placedReader v ord).encode h ++ rest := by
  obtain ⟨sites, eqn, stream⟩ := reader_some A T m older cap desc read
  obtain ⟨h, data⟩ := exists_placed X v ord out.value (sites.trans order)
  refine ⟨h, ⟨data ▸ eqn, ?_⟩, fun y hy => children_injective v ord ?_⟩
  · rw [← children_bits, data, stream]
  · exact (congrArg Outcome.value hy.1).symm.trans data.symm

variable {R L : Type} [CommRing R] [Fintype L] {κ : L → R} {t : Term R X.network}

/-- The actual native writes on the semantic witness establish exactly the
typed packets carried by the local vertex job. -/
theorem reader_childPackets (r : TermParsers κ t) (hp : ∀ u h, r.halfBits u h = packed X u h)
    (v : t.output.Site) (node : Word w) (saved : Scratch w endAddr)
    (order : (desc node).sites = List.ofFn fun j => ((r.order.children v).entries j).val)
    (h : Placed t.place X.network.Half v) (rest : List Bool) :
    let xs := children X v (r.order.children v) h
    let qs := r.childPackets (childNode X older cap) v h
    ∃ out, reader A T m older cap desc node saved (qs.flatMap Packet.bits ++ rest) =
        some (out, rest) ∧ out.value = xs ∧ out.updated = writePackets A qs saved := by
  intro xs qs
  have packets := children_packets r hp older cap v h
  change xs.map (Child.packet X older cap) = qs at packets
  have bits : qs.flatMap Packet.bits = (placedReader v (r.order.children v)).encode h := by
    rw [← packets, List.flatMap_map]
    exact children_bits v (r.order.children v) h
  refine ⟨outcome A T m older cap desc node saved xs, ?_, rfl, ?_⟩
  · rw [bits]
    exact reader_placed A T m older cap desc v (r.order.children v) node saved order h rest
  · rw [← packets]; rfl

end PairSimulation.ShrinkRole.ChildArguments

end VPVNP
end Computability
end OAI
