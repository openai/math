import OAI.Computability.VPVNP.PairNodeChildSlots
import OAI.Computability.VPVNP.PairPendingArguments
import OAI.Computability.VPVNP.PairTraversalRows

/-!
# Ordered arguments at the child addresses in a descriptor row

Each child keeps its old site number, its actual outgoing and incoming
half-wire coordinates, and its absolute DFS node. Machine writes to these
addresses give the same scratch update as the logical list of packets.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments.ChildScan

open BurstRAM BurstRAM.PrivateRAM LocalHistory Compression TraversalRows DFS
open scoped Fin.CommRing

variable {w a g endAddr : ℕ} (X : State a g)

/-- An old site and all independent field values guessed there. -/
structure Child where
  /-- Site in the older network whose descriptor row and incidence widths determine this
  child’s argument buffer and field lengths. -/
  site : X.network.Site
  /-- Independent bit values for every outgoing and incoming slot at the child site, indexed
  within the actual half-wire width of that slot. -/
  data : (i : Bool × Fin (2 ^ a)) → Fin (X.halfWidth site i.1 i.2) → Bool

/-- Forms a child record from a network half-wire assignment by reading its coordinates in the
outgoing and incoming incidence orders of the site. -/
noncomputable def Child.ofHalf (u : X.network.Site) (h : X.network.Half u) : Child X :=
  ⟨u, fun i => fieldBits X u h i.1 i.2⟩

/-- Absolute DFS descriptor address of the old site, obtained from its ordinal in site order
and the row layout with base older and capacity cap. -/
def childNode (older cap : ℕ) (u : X.network.Site) : ℕ := (sitePointers cap older (siteOrder X) u).1

/-- Serializes the child’s fields in port order, first for outgoing ports and then for incoming
ports. Each field contributes exactly its own bits. -/
noncomputable def Child.payload (v : Child X) : List Bool :=
  ChildSlots.bits X v.site v.data (ChildSlots.slots (2 ^ a))

/-- Pairs the child’s absolute descriptor address with its serialized half-wire bits so the
pending-argument arena can store the payload at the corresponding node. -/
noncomputable def Child.packet (older cap : ℕ) (v : Child X) : Packet :=
  ⟨childNode X older cap v.site, v.payload X⟩

theorem Child.payload_ofHalf (u : X.network.Site) (h : X.network.Half u) :
    (Child.ofHalf X u h).payload X = packed X u h := ChildSlots.bits_all h

private theorem field_lengths (u : X.network.Site)
    (data : (i : Bool × Fin (2 ^ a)) → Fin (X.halfWidth u i.1 i.2) → Bool)
    (slots : List (Bool × Fin (2 ^ a))) :
    (ChildSlots.bits X u data slots).length = ChildSlots.length X u slots := by
  simp [ChildSlots.bits, ChildSlots.length, List.flatMap_def, Function.comp_def]

theorem Child.payload_length (v : Child X) :
    (v.payload X).length = ChildSlots.length X v.site (ChildSlots.slots (2 ^ a)) :=
  field_lengths X v.site v.data _

/-- Any complete prefix is a possible independent assignment to the half-wire
fields. Width-zero fields contribute an empty segment. -/
private theorem choose_slots (u : X.network.Site) (slots : List (Bool × Fin (2 ^ a)))
    (nd : slots.Nodup) (bs : List Bool) (h : ChildSlots.length X u slots ≤ bs.length) :
    ∃ data, ChildSlots.bits X u data slots ++ bs.drop (ChildSlots.length X u slots) = bs := by
  classical
  induction slots generalizing bs with
  | nil => exact ⟨fun _ _ => false, rfl⟩
  | cons i rest ih =>
    let n := X.halfWidth u i.1 i.2
    have hl : ChildSlots.length X u (i :: rest) = n + ChildSlots.length X u rest := by
      simp [ChildSlots.length, n]
    obtain ⟨tail, ht⟩ := ih (List.nodup_cons.mp nd).2 (bs.drop n) (by rw [hl] at h; simp; omega)
    have hn : n ≤ bs.length := (Nat.le_add_right _ _).trans (hl ▸ h)
    let head : Fin n → Bool := fun j => bs[j.val]'(j.isLt.trans_le hn)
    let d := Function.update tail i head
    have he : List.ofFn head = bs.take n := by
      apply List.ext_getElem (by simp [hn])
      intros
      simp [head]
    have same : ChildSlots.bits X u d rest = ChildSlots.bits X u tail rest := by
      unfold ChildSlots.bits
      simp only [List.flatMap_def]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro j hj
      rw [show d j = tail j from Function.update_of_ne
        (fun (eqn : j = i) => (List.nodup_cons.mp nd).1 (eqn ▸ hj)) ..]
    refine ⟨d, ?_⟩
    change (List.ofFn (d i) ++ ChildSlots.bits X u d rest) ++ _ = _
    rw [show d i = head from Function.update_self .., he, same, hl, List.append_assoc,
      ← List.drop_drop, ht, List.take_append_drop]

/-- Split off precisely one full child's half-wire packet from an arbitrary tape. -/
theorem choose_payload (u : X.network.Site) (bs : List Bool)
    (h : ChildSlots.length X u (ChildSlots.slots (2 ^ a)) ≤ bs.length) :
    ∃ d : Child X, d.site = u ∧ d.payload X ++ bs.drop (d.payload X).length = bs := by
  have nd : (ChildSlots.slots (2 ^ a)).Nodup := by
    rw [ChildSlots.slots, List.nodup_append]
    refine ⟨List.nodup_ofFn.mpr (fun _ _ e => congrArg Prod.snd e),
      List.nodup_ofFn.mpr (fun _ _ e => congrArg Prod.snd e), ?_⟩
    intro x hx y hy he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    cases he
  obtain ⟨data, hd⟩ := choose_slots X u _ nd bs h
  let child : Child X := ⟨u, data⟩
  exact ⟨child, rfl, by rw [Child.payload_length]; exact hd⟩

/-- Actual ordered old-site arguments of a parent term. -/
noncomputable def children {A : Type*} {t : NetworkKernel.Term A X.network}
    (v : t.output.Site) (ord : Order (t.Preimage v))
    (h : NetworkKernel.Placed t.place X.network.Half v) :
    List (Child X) := List.ofFn fun j => Child.ofHalf X (ord.entries j).val
      (h (ord.entries j).val (ord.entries j).prop)

variable {X}

/-- Applying native stores for a list of complete child packets. -/
def storePackets (A : Arena) (qs : List Packet) (priv : Word w → Word w) : Word w → Word w :=
  qs.foldl (fun prev q => PrivateFields.storeBits (A.base q.node) q.bits prev) priv

private theorem store_congr (dst : ℕ) (bs : List Bool) (f g : Word w → Word w) (x : Word w)
    (hx : f x = g x) : PrivateFields.storeBits dst bs f x = PrivateFields.storeBits dst bs g x := by
  induction bs generalizing dst f g with
  | nil => exact hx
  | cons b rest ih =>
    apply ih
    by_cases he : x = (dst : Word w)
    · subst x
      simp
    · simpa [Function.update_of_ne he] using hx

/-- Projection of the native private memory after all writes is exactly the
logical scratch update for the list of packets. -/
theorem scratch_storePackets (A : Arena) (qs : List Packet) (priv : Word w → Word w) :
    scratch endAddr (storePackets A qs priv) = writePackets A qs (scratch endAddr priv) := by
  induction qs generalizing priv with
  | nil => rfl
  | cons q rest ih =>
    change scratch endAddr
      (storePackets A rest (PrivateFields.storeBits (A.base q.node) q.bits priv)) =
      writePackets A rest (q.write A (scratch endAddr priv))
    rw [ih]
    congr 1
    funext x
    apply store_congr
    simp [rawScratch, scratch, x.prop]

end PairSimulation.NodeArguments.ChildScan

end VPVNP
end Computability
end OAI
