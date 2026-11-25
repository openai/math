import OAI.Computability.BorderVNP.FiniteEvaluatorCubePacket
import OAI.Computability.BorderVNP.RoutingISACubeConstantArena
import OAI.Computability.BorderVNP.RoutingISAExtendedFrame

/-! # Native construction and lookup of the finite-field cube deck

The compiled initializer synthesizes each fixed field word from ordinary binary
instructions. A team then reads the word at the selector, vertex and incident
digits actually supplied by its packet assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeDeck

open VPVNP.BurstRAM RoutingISA BorderVNP.Cube BorderVNP.Cube.Tally DiagonalTallyPacketEmit
open scoped Classical

variable {F : Type*} [Fintype F] {n b h K s w : ℕ}
variable (table : TableEntry n b h K s → F)

/-- Word stored at the Boolean argument of one physical cube table. -/
noncomputable def entry (e : TableEntry n b h K s) : ℕ := CubeWord.encode (table e)

/-- The common initializer depends on the chosen finite cube identity and table. -/
noncomputable def install : Code := CubeConstants.install (entry table)

variable (f : Frame) (fresh : ℕ)

local notation "frame" => CubeConstants.inArena f fresh n b h K s
local notation "ptr" => CubeConstants.idBase fresh n b h K s
local notation "stop" => CubeConstants.arenaEnd fresh (entry table)

/-- The four physical cube operands at their allocated addresses. -/
structure WordsAt (id : TableEntry n b h K s → ℕ) (mem : ℕ → ℕ) : Prop where
  recipe : Frame.recipeAt frame mem n b h K s
  words : ∀ k < 2^argumentWidth n b h K s, mem (ptr+k) =
    idTable (selectorOrder n K h) (vertexOrder _) id k
  zero : mem fresh = 0
  one : mem (fresh+1) = 1

/-- The finite deck stores the framed one-hot scalar words for its given field. -/
abbrev At (mem : ℕ → ℕ) := WordsAt f fresh (entry table) mem

private theorem word_end (id : TableEntry n b h K s → ℕ) : CubeConstants.arenaEnd fresh id = ptr+2^argumentWidth n b h K s := by
  simp only [CubeConstants.arenaEnd,CubeConstants.ids,List.length_ofFn]

private theorem recipe_addr (u : Selector n K h) (v : Vertex (n+1))
    (j : ℕ) (hj : j < (recipe u v b s).length) :
    fresh+2+((selectorOrder n K h u).val * Fintype.card (Vertex (n+1))+
      (vertexOrder _ v).val)*argumentWidth n b h K s+j < ptr := by
  let i : Fin (argumentWidth n b h K s) := ⟨j,(recipe_length u v b s) ▸ hj⟩
  have index := CubeConstants.recipeIndex_val u v i
  have room := (CubeConstants.recipeIndex u v i).isLt
  change _ = _+j at index
  simp only [CubeConstants.idBase,CubeConstants.recipes,List.length_ofFn]
  omega

/-- The deck survives any intervening computation that preserves its physical
interval. The dynamic frame may change its owned-vertex count and triple bank. -/
theorem WordsAt.preserve (id : TableEntry n b h K s → ℕ) {mem mem' : ℕ → ℕ}
    (actual : WordsAt f fresh id mem) (f' : Frame)
    (keep : ∀ a, fresh ≤ a → a < CubeConstants.arenaEnd fresh id → mem' a = mem a) : WordsAt f' fresh id mem' := by
  have ends := word_end fresh id
  have starts : fresh+2 ≤ ptr := Nat.le_add_right ..
  have leEnd : ptr ≤ CubeConstants.arenaEnd fresh id := ends.symm ▸ Nat.le_add_right _ _
  refine ⟨⟨rfl,rfl,?_⟩,?_,?_,?_⟩
  · intro u v j hj
    have bound := recipe_addr fresh u v j hj
    dsimp only [CubeConstants.inArena]
    exact (keep _ (by omega) (bound.trans_le leEnd)).trans (actual.recipe.2.2 u v j hj)
  · intro k hk
    exact (keep _ (by omega) (by omega)).trans (actual.words k hk)
  · exact (keep _ le_rfl (by omega)).trans actual.zero
  · exact (keep _ (by omega) (by omega)).trans actual.one

/-- Transport the framed finite-scalar deck over its real immutable words. -/
theorem At.preserve {mem mem' : ℕ → ℕ} (actual : At table f fresh mem) (f' : Frame)
    (keep : ∀ a, fresh ≤ a → a < stop → mem' a = mem a) : At table f' fresh mem' :=
  WordsAt.preserve f fresh (entry table) actual f' keep

/-- Four pointers and the two static recipe dimensions in the length-advice
frame. The other frame entries remain available to the other native stages. -/
noncomputable def pointers (old : Fin 81 → Word w) (fresh n b h K s : ℕ) : Fin 81 → Word w :=
  let words := Function.update (Function.update (Function.update (Function.update old 50 (Fin.ofNat _ fresh))
    51 (Fin.ofNat _ (fresh+1))) 48 (Fin.ofNat _ (fresh+2))) 16 (Fin.ofNat _ (CubeConstants.idBase fresh n b h K s))
  Function.update (Function.update words 52 (Fin.ofNat _ (argumentWidth n b h K s))) 53
    (Fin.ofNat _ (Fintype.card (Vertex (n+1))))

/-- The actual 81-word boot image supplies all four initializer pointers. -/
theorem fields_boot (old : Fin 81 → Word w) (base : ℕ) (mem : Memory w)
    (room : ptr < 2^w) :
    CubeConstants.Fields frame base ptr (readings (ExtendedFrame.installed mem base (pointers old fresh n b h K s))) := by
  have starts : fresh+2 ≤ ptr := Nat.le_add_right ..
  have atIndex (j : Fin 81) := congrArg Fin.val (ExtendedFrame.installed_at mem base (pointers old fresh n b h K s) j)
  unfold CubeConstants.Fields
  dsimp only [CubeConstants.inArena,readings]
  refine ⟨?_,?_,?_,?_⟩
  all_goals first | apply (atIndex 50).trans | apply (atIndex 51).trans | apply (atIndex 48).trans | apply (atIndex 16).trans
  all_goals simp (config := {decide := true}) [pointers,Nat.mod_eq_of_lt (show fresh<2^w by omega),
    Nat.mod_eq_of_lt (show fresh+1<2^w by omega),Nat.mod_eq_of_lt (show fresh+2<2^w by omega),Nat.mod_eq_of_lt room]

/-- The recipe dimensions supplied in the boot image agree with the actual cube. -/
theorem dimensions_boot (old : Fin 81 → Word w) (base : ℕ) (mem : Memory w)
    (room : ptr+2^argumentWidth n b h K s < 2^w) :
    let loaded := readings (ExtendedFrame.installed mem base (pointers old fresh n b h K s))
    loaded (base+83)=argumentWidth n b h K s ∧ loaded (base+84)=Fintype.card (Vertex (n+1)) := by
  intro loaded
  have length : argumentWidth n b h K s < 2^w := Nat.lt_two_pow_self.trans
    ((Nat.le_add_left _ _).trans_lt room)
  have vertex : Fintype.card (Vertex (n+1)) < 2^w :=
    (Nat.le_pow_clog (by decide) _).trans_lt ((Nat.pow_le_pow_right (by decide : 0<2)
      (show Nat.clog 2 (Fintype.card (Vertex (n+1))) ≤ argumentWidth n b h K s by unfold argumentWidth; omega)).trans_lt
      ((Nat.le_add_left _ _).trans_lt room))
  have word (j : Fin 81) := congrArg Fin.val (ExtendedFrame.installed_at mem base (pointers old fresh n b h K s) j)
  exact ⟨(word 52).trans (by simp [pointers,Nat.mod_eq_of_lt length]),
    (word 53).trans (by simpa only [pointers,Function.update_self,Fin.val_ofNat] using Nat.mod_eq_of_lt vertex)⟩

/-- A fixed width works for every assignment of field values to this cube
identity. The bound depends only on the recipe shape and the field size. -/
noncomputable def minimumWidth (F : Type*) [Fintype F] (n b h K s : ℕ) : ℕ :=
  max (CubeConstants.recipes n b h K s).sum.size (2*Fintype.card F+1)

/-- All the installer operands fit from the common width threshold and the
one-past address of the fixed deck. This includes unused Boolean table rows. -/
theorem fits (base : ℕ) (frameRoom : base+112 ≤ fresh) (address : stop < 2^w)
    (wide : minimumWidth F n b h K s ≤ w) : CubeConstants.Fits frame w base ptr (entry table) := by
  have values := max_le_iff.mp wide
  refine ⟨frameRoom,by simp [CubeConstants.inArena],by simp [CubeConstants.inArena],le_rfl,address,?_,?_⟩
  · intro x hx
    exact (List.le_sum_of_mem hx).trans_lt ((Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by decide) values.1))
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    unfold idTable
    split
    · exact (CubeWord.encode_lt _).trans_le (Nat.pow_le_pow_right (by decide) values.2)
    · exact Nat.two_pow_pos _

/-- Native deterministic boot from the four delivered addresses. It constructs
the entire fixed deck in a constant tick budget and preserves the routed input
below the arena. The scalar table contents are never assumed resident. -/
theorem install_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : Bank w) (mem : Memory w)
    (frameRoom : (pub 0).val+112 ≤ fresh) (address : stop < 2^w)
    (wide : minimumWidth F n b h K s ≤ w)
    (fields : CubeConstants.Fields frame (pub 0).val ptr (readings mem)) :
    ∃ es t mt, Runs pub mac (install table) bank mem es t mt ∧ traceCost es ≤ (install table).slots ∧
      At table f fresh (readings mt) ∧ (∀ a < fresh, mt a = mem a) ∧
      (∀ e ∈ es, e.choices = [] ∧ e.sign = .plus) := by
  have fit := fits table f fresh (pub 0).val frameRoom address wide
  obtain ⟨es,t,mt,run,cost,image⟩ := CubeConstants.install_run pub mac bank mem frame ptr (entry table) fit fields
  change readings mt = CubeConstants.image frame ptr (entry table) (readings mem) at image
  obtain ⟨rec,deck,zero,one⟩ := CubeConstants.image_values frame (entry table) (readings mem) fit rfl rfl
  refine ⟨es,t,mt,run,cost,?_,?_,run.unsigned_events (CubeConstants.install_unsigned _).1⟩
  · rw [image]; exact ⟨rec,deck,zero,one⟩
  · intro a ha
    apply Fin.ext
    change readings mt a = readings mem a
    rw [image,CubeConstants.image_before frame ptr (entry table) _ fit a ha]

/-- Every actual initializer run has only ordinary, positive events and has a
unique trace, bank and memory endpoint. Its contribution to any field path is one. -/
theorem install_effect [Field F] {Q Γ : Type} {m g : ℕ} (pub : Arg → Word w)
    (lib : Fin 8 → TeamSite.Macro Q Γ m g) (ret : FieldProcessor.Returns Q Γ F m 8) (fuel : ℕ)
    {bank mem es t mt} (run : Runs pub (TeamSiteEvents.macros lib fuel) (install table) bank mem es t mt)
    (cost : traceCost es ≤ (install table).slots) :
    TeamContraction.Within (install table).slots 0 0 es ∧
      weight pub lib ret fuel (install table) bank es = 1 ∧
      ∀ fs u mu, Runs pub (TeamSiteEvents.macros lib fuel) (install table) bank mem fs u mu → fs=es ∧ u=t ∧ mu=mt := by
  have unsigned := (CubeConstants.install_unsigned (entry table)).1
  have det (c : Code) (yes : c.unsigned = true) : c.deterministic = true := by
    induction c <;> simp_all [Code.unsigned,Code.deterministic]
  have deterministic := det (install table) unsigned
  have clean := run.unsigned_events unsigned
  refine ⟨⟨cost,fun e he => (run.deterministic_extra deterministic e he).le,?_⟩,?_,?_⟩
  · intro e he; rw [(clean e he).1]; rfl
  · exact FiniteDiagonal.pathProduct_ordinary_positive _ _ _ _ _ _ _ (TeamRAM.execute_spec run.execute).1
      (FiniteDiagonal.ordinary_of_deterministic run deterministic) (fun e he => (clean e he).2)
  · intro fs u mu other
    exact other.unique_of_deterministic deterministic run

private theorem relative_lt (u : Selector n K h) (v : Vertex (n+1)) {j : ℕ}
    (atDigit : Reference.packet j ∈ Tally.recipe u v b s) : j < bankWidth n b h K s := by
  simp only [Tally.recipe,List.mem_append,List.mem_reverse,List.mem_ofFn] at atDigit
  rcases atDigit with ((⟨i,hi⟩ | lit) | pad) | ⟨i,hi⟩
  · have eq := Reference.packet.inj hi
    have room : selectorWidth n K h ≤ bankWidth n b h K s := by
      unfold bankWidth supplyBase; omega
    exact eq ▸ i.isLt.trans_le room
  · obtain ⟨digit,_,bad⟩ := List.mem_map.mp lit
    cases bad
  · have bad := List.eq_of_mem_replicate pad
    cases bad
  · exact (Reference.packet.inj hi) ▸ rowOffset_lt u v _

private theorem references_below (id : TableEntry n b h K s → ℕ) (visit : Visit n b h K s)
    (endDeck : CubeConstants.arenaEnd fresh id ≤ f.descriptors)
    (bank : visit.base + bankWidth n b h K s ≤ f.descriptors) :
    ∀ r ∈ Tally.recipe visit.selector visit.vertex b s,
      r.address visit.base fresh (fresh+1) < f.descriptors := by
  have p : fresh+2 ≤ ptr := Nat.le_add_right ..
  have bounds : ptr ≤ CubeConstants.arenaEnd fresh id := (word_end fresh id).symm ▸ Nat.le_add_right _ _
  intro r hr
  cases r with
  | literal digit => cases digit <;> dsimp only [Reference.address] <;> omega
  | packet j =>
    have := relative_lt visit.selector visit.vertex hr
    change visit.base+j < _; omega

/-- Actual finite evaluator inputs with the common contiguous deck and runtime
owned-vertex columns. -/
noncomputable def inputs (visits : Fin f.count → Visit n b h K s) (dst demand : ℕ) : CubePacket.Inputs n b h K s F :=
  ⟨frame,visits,table,ptr,dst,demand⟩

omit [Fintype F] in
/-- Assemble the full native cube lookup precondition from the installed deck,
the actual routed packet visits, and ordinary address bounds. All data-dependent
recipe offsets and selected slice bounds are derived from the triples. -/
theorem wordPrepared (id : TableEntry n b h K s → ℕ) (visits : Fin f.count → Visit n b h K s) (dst demand : ℕ)
    (pub : Arg → Word w) (mem : Memory w) (deck : WordsAt f fresh id (readings mem))
    (loaded : Frame.resident frame (readings pub) (readings mem))
    (triples : ∀ i, (visits i).tripleAt (readings mem) (f.triples+3*i.val))
    (banks : ∀ i, VertexAt mem (visits i).base (visits i).selector (visits i).vertex (visits i).ends (visits i).supply)
    (tableWord : (mem ((pub 0).val+47)).val=ptr) (dstWord : (mem ((pub 0).val+71)).val=dst)
    (frameRoom : (pub 0).val+112 ≤ fresh) (tableRoom : CubeConstants.arenaEnd fresh id ≤ f.descriptors)
    (tripleRoom : f.triples+3*f.count ≤ f.descriptors) (banksRoom : ∀ i, (visits i).base+bankWidth n b h K s ≤ f.descriptors)
    (outputs : f.descriptors+2*f.count ≤ f.refs) (separate : f.refs+f.count*argumentWidth n b h K s ≤ dst)
    (room : dst+f.count < 2^w) : CubePacket.WordPrepared (inputs table f fresh visits dst demand) id pub mem := by
  let width := argumentWidth n b h K s
  change f.refs+f.count*width ≤ dst at separate
  let vertices := Fintype.card (Vertex (n+1))
  let total := Fintype.card (Selector n K h)*vertices
  have lePtr : fresh+2 ≤ ptr := Nat.le_add_right ..
  have leEnd : ptr ≤ CubeConstants.arenaEnd fresh id := (word_end fresh id).symm ▸ Nat.le_add_right _ _
  have dataRoom : ptr+2^width ≤ f.descriptors := (word_end fresh id).symm ▸ tableRoom
  have refsRoom : f.refs+f.count*width < 2^w := by omega
  have arenaRoom : f.descriptors < 2^w := by omega
  have below (i : Fin f.count) := references_below f fresh id (visits i) tableRoom (banksRoom i)
  have slice (i : Fin f.count) : (selectorOrder n K h (visits i).selector).val * vertices +
      (vertexOrder _ (visits i).vertex).val < 2^w := by
    have hi := Nat.mul_le_mul_right vertices (selectorOrder n K h (visits i).selector).isLt
    rw [Nat.succ_mul] at hi
    have hv : (vertexOrder _ (visits i).vertex).val < vertices := (vertexOrder _ _).isLt
    have bound : total ≤ 2^width := by
      dsimp only [total,vertices,width,argumentWidth,selectorWidth]
      rw [pow_add,pow_add]
      exact (Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _)).trans
        (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
    change Fintype.card (Selector n K h)*vertices ≤ _ at bound
    omega
  have fits : Frame.Fits frame (readings mem) w (pub 0).val := by
    refine ⟨by dsimp [CubeConstants.inArena]; omega,tripleRoom,?_,outputs,refsRoom,?_,?_⟩
    · intro k hk j hj
      let i : Fin f.count := ⟨k,hk⟩
      obtain ⟨_,sel,vertex⟩ := triples i
      have addr := recipe_addr fresh (visits i).selector (visits i).vertex j
        (by rw [recipe_length]; exact hj)
      unfold Frame.recipeAddr
      dsimp only [CubeConstants.inArena]
      rw [sel,vertex]
      exact addr.trans_le (leEnd.trans tableRoom)
    · intro k hk
      change k < f.count*width at hk
      have pos : 0<width := by by_contra! hz; rw [show width=0 by omega,Nat.mul_zero] at hk; omega
      let i : Fin f.count := ⟨k/width,(Nat.div_lt_iff_lt_mul pos).mpr hk⟩
      let j := k%width
      have hj : j < width := Nat.mod_lt _ pos
      have eq : i.val*width+j=k := Nat.div_add_mod' ..
      have out := (visits i).generatedRef frame (readings mem) i.val deck.recipe (triples i) hj
      change Frame.refValue frame (readings mem) (i.val*width+j) = _ at out
      rw [← eq,out]
      exact (below i _ (List.getElem_mem _)).trans arenaRoom
    · intro k hk
      let i : Fin f.count := ⟨k,hk⟩
      obtain ⟨_,sel,vertex⟩ := triples i
      dsimp only [CubeConstants.inArena]
      rw [sel,vertex]
      exact slice i
  exact ⟨loaded,fits,deck.recipe,triples,banks,deck.zero,deck.one,below,tableWord,dstWord,deck.words,dataRoom,separate,room⟩

/-- The installed scalar framing is the finite evaluator specialization of the native word reader. -/
theorem prepared (visits : Fin f.count → Visit n b h K s) (dst demand : ℕ)
    (pub : Arg → Word w) (mem : Memory w) (deck : At table f fresh (readings mem))
    (loaded : Frame.resident frame (readings pub) (readings mem))
    (triples : ∀ i, (visits i).tripleAt (readings mem) (f.triples+3*i.val))
    (banks : ∀ i, VertexAt mem (visits i).base (visits i).selector (visits i).vertex (visits i).ends (visits i).supply)
    (tableWord : (mem ((pub 0).val+47)).val=ptr) (dstWord : (mem ((pub 0).val+71)).val=dst)
    (frameRoom : (pub 0).val+112 ≤ fresh) (tableRoom : stop ≤ f.descriptors)
    (tripleRoom : f.triples+3*f.count ≤ f.descriptors) (banksRoom : ∀ i, (visits i).base+bankWidth n b h K s ≤ f.descriptors)
    (outputs : f.descriptors+2*f.count ≤ f.refs) (separate : f.refs+f.count*argumentWidth n b h K s ≤ dst)
    (room : dst+f.count < 2^w) : CubePacket.Prepared (inputs table f fresh visits dst demand) pub mem :=
  wordPrepared table f fresh (entry table) visits dst demand pub mem deck loaded triples banks tableWord dstWord
    frameRoom tableRoom tripleRoom banksRoom outputs separate room

end FiniteEvaluator.CubeDeck

end BorderVNP
end Computability
end OAI
