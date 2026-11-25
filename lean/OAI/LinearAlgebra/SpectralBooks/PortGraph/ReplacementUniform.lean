import OAI.LinearAlgebra.SpectralBooks.DecoratedMaps.DecoratedMapClass
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementDecoder

/-!
# Compiling the replacement tests into the uniform table

A decoration names the saved patch record, its list index and a role in that
tree. An edge test reads only the two endpoint headers of the uniform table.
The two role names and their port numbers identify the prescribed ends of the
replacement. The decoder consequently sees exactly the vertex and edge tests
used to reconstruct a replacement.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace PortGraph.ReplacementTemplate

open UniformDecorations

variable {J I : Type*} (T : J → ReplacementTemplate)

abbrev RoleLabel := (j : J) × (T j).Role

/-- The bounded role name is a fixed-width decoration. -/
def roleCode [Fintype (RoleLabel T)] {h : ℕ} (size : Fintype.card (RoleLabel T) ≤ 2^h) :
    RoleLabel T ↪ Bits h := (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb size)

private def slot4 (θ : MapType) (i : Fin θ.degree.val) : Fin 4 :=
  i.castLE (Nat.le_of_lt_succ θ.degree.isLt)

/-- Consecutive port numbers, embedded in the four available slots. -/
def actualSlots {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (M : RootedMap V E) :
    M.graph.FourPortNumbering := fun v => (M.num v).toEmbedding.trans (Fin.castLEEmb (M.degree v))

/-- The tests fixed by the finite catalogue. A tag consists of both an old
patch record and its position in that record's list. -/
structure LocalRules where
  slot : Numbering T
  patchId : J → I
  oldEdge : (Σ j, (T j).Stub) → (Σ j, (T j).Stub) → Prop
  recordOK : J → Prop
  marked : RoleLabel T → Prop

namespace LocalRules

variable {T} (R : LocalRules (I := I) T)

def Fits (θ : MapType) (a : RoleLabel T) : Prop :=
  ∀ (i : Fin 4) (b : Bool),
    (∃ k : Fin θ.degree.val, slot4 θ k = i ∧ θ.direction k = b) ↔
      ∃ u : RolePort T a, R.slot a u = i ∧ side T u.val = b

variable {s h : ℕ} (code : RoleLabel T ↪ Bits h)

/-- One type/slot header identifies an end from its role and numbered port. -/
def AtHeader (x : Bits h × Tag) (u : End T) : Prop :=
  code (owner T u) = x.1 ∧ endNumber R.slot u = slot4 x.2.1 x.2.2

/-- Entry at a named role, read in the port order of the uniform table. -/
def entry {K : Type*} [Zero K] (coefficient : (a : RoleLabel T) → (RolePort T a → Bits s) → K)
    (θ : MapType) (d : Bits h) (x : Fin θ.degree.val → Bits s) : K :=
  if ha : ∃ a, code a = d then
    let a := ha.choose
    if hn : ∀ u, (R.slot a u).val < θ.degree.val then
      coefficient a (fun u => x ⟨(R.slot a u).val,hn u⟩) else 0
  else 0

/-- The single, map-independent specification used on every compressed map. -/
def spec {K : Type*} [Zero K] (coefficient : (a : RoleLabel T) → (RolePort T a → Bits s) → K) :
    Spec K s h where
  vertexOK θ d := ∃ a, code a = d ∧ R.recordOK a.1 ∧ (R.marked a ↔ θ.root = true) ∧ R.Fits θ a
  edgeOK x y := ∃ u v, R.AtHeader code x u ∧ R.AtHeader code y v ∧ PairTest R.patchId R.oldEdge u v
  tensor := R.entry code coefficient

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (M : RootedMap V E)

private theorem fits_iff (z : V → RoleLabel T) (v : V) :
    R.Fits (M.typeAt v) (z v) ↔ VertexTest T (actualSlots M) R.slot z v := by
  have port (i : Fin 4) (b : Bool) :
      (∃ k : Fin (M.typeAt v).degree.val, slot4 _ k = i ∧ (M.typeAt v).direction k = b) ↔
      (∃ p : M.graph.Port v, actualSlots M v p = i ∧ p.val.2 = b) := by
    constructor
    · rintro ⟨k,hk,hb⟩
      refine ⟨(M.num v).symm k, ?_,hb⟩
      exact ((congrArg (slot4 (M.typeAt v)) ((M.num v).apply_symm_apply k))).trans hk
    · rintro ⟨p,hp,hb⟩
      refine ⟨M.num v p,hp,?_⟩
      exact ((view M).direction_slot v p).trans hb
  unfold Fits VertexTest
  simp only [port]

/-- The decoder's exact vertex, root and pairing checks for an actual map. -/
def Accepts (z : V → RoleLabel T) : Prop :=
  (∀ v, R.recordOK (z v).1) ∧ (∀ v, R.marked (z v) ↔ v = M.root) ∧
    ∃ hv : ∀ v, VertexTest T (actualSlots M) R.slot z v,
      ∀ e, PairTest R.patchId R.oldEdge (readEnd hv e false) (readEnd hv e true)

private theorem end_ext {u w : End T} (ho : owner T u = owner T w)
    (hn : endNumber R.slot u = endNumber R.slot w) : u = w := by
  have number {a : RoleLabel T} (p : End T) (hp : owner T p = a) :
      R.slot a ⟨p,hp⟩ = endNumber R.slot p := by subst a; rfl
  have he := (R.slot (owner T w)).injective ((number u ho).trans hn)
  exact congrArg Subtype.val he

private theorem header_iff (z : V → RoleLabel T)
    (hv : ∀ v, VertexTest T (actualSlots M) R.slot z v) (e : E) (b : Bool) (u : End T) :
    R.AtHeader code ((view M).endpoint (code ∘ z) e b) u ↔ u = readEnd hv e b := by
  have ownerEq := owner_readEnd hv e b
  have slotEq := number_readEnd hv e b
  constructor
  · rintro ⟨hc,hs⟩
    exact R.end_ext ((code.injective hc).trans ownerEq.symm) (hs.trans slotEq.symm)
  · rintro rfl
    exact ⟨congrArg code ownerEq,slotEq⟩

variable {K : Type*} [Zero K] (coefficient : (a : RoleLabel T) → (RolePort T a → Bits s) → K)

theorem valid_encoded_iff (z : V → RoleLabel T) :
    (R.spec code coefficient).Valid (view M) (code ∘ z) ↔ R.Accepts M z := by
  have vertex (v : V) :
      (R.spec code coefficient).vertexOK (M.typeAt v) (code (z v)) ↔
        R.recordOK (z v).1 ∧ (R.marked (z v) ↔ v = M.root) ∧
        VertexTest T (actualSlots M) R.slot z v := by
    change (∃ a, code a = code (z v) ∧ _) ↔ _
    have root : (M.typeAt v).root = true ↔ v = M.root := by simp [RootedMap.typeAt]
    simp only [EmbeddingLike.apply_eq_iff_eq, root]
    constructor
    · rintro ⟨_,rfl,hR,hM,hF⟩
      exact ⟨hR,hM,(R.fits_iff M z v).mp hF⟩
    · rintro ⟨hR,hM,hF⟩
      exact ⟨_,rfl,hR,hM,(R.fits_iff M z v).mpr hF⟩
  have edges (hv : ∀ v, VertexTest T (actualSlots M) R.slot z v) (e : E) :
      (R.spec code coefficient).edgeOK ((view M).endpoint (code ∘ z) e false)
        ((view M).endpoint (code ∘ z) e true) ↔
        PairTest R.patchId R.oldEdge (readEnd hv e false) (readEnd hv e true) := by
    change (∃ u v, R.AtHeader _ _ _ ∧ R.AtHeader _ _ _ ∧ _) ↔ _
    simp only [R.header_iff code M z hv]
    constructor
    · rintro ⟨_,_,rfl,rfl,hh⟩
      exact hh
    · intro hh
      exact ⟨_,_,rfl,rfl,hh⟩
  constructor
  · rintro ⟨hV,hE⟩
    have hs := fun v => (vertex v).mp (hV v)
    let hv := fun v => (hs v).2.2
    exact ⟨fun v => (hs v).1, fun v => (hs v).2.1, hv, fun e => (edges hv e).mp (hE e)⟩
  · rintro ⟨hR,hM,hv,he⟩
    exact ⟨fun v => (vertex v).mpr ⟨hR v,hM v,hv v⟩, fun e => (edges hv e).mpr (he e)⟩

/-- Acceptance rejects all unused words, and a passing word at every vertex
decodes to exactly one assignment of roles passing the decoder tests. -/
theorem valid_iff (d : V → Bits h) :
    (R.spec code coefficient).Valid (view M) d ↔
      ∃! z : V → RoleLabel T, code ∘ z = d ∧ R.Accepts M z := by
  constructor
  · intro ok
    choose z hc _ using ok.1
    have hd : code ∘ z = d := funext hc
    refine ⟨z,⟨hd,(R.valid_encoded_iff code M coefficient z).mp (hd ▸ ok)⟩,?_⟩
    exact fun z' hz' => funext fun v => code.injective (congrFun (hz'.1.trans hd.symm) v)
  · rintro ⟨z,⟨rfl,hz⟩,_⟩
    exact (R.valid_encoded_iff code M coefficient z).mpr hz

/-- On an occupied type, the local tensor receives each wire index at the
actual port corresponding to the prescribed role port. -/
theorem entry_at_role (z : V → RoleLabel T) (hv : ∀ v, VertexTest T (actualSlots M) R.slot z v)
    (v : V) (x : M.graph.Port v → Bits s) :
    (R.spec code coefficient).tensor (M.typeAt v) (code (z v))
      (fun i => x ((M.num v).symm i)) =
    coefficient (z v) (fun u => x ((Equiv.ofBijective _ (readPort_bijective hv v)).symm u)) := by
  have num (u : RolePort T (z v)) :
      R.slot (z v) u = actualSlots M v ((Equiv.ofBijective _ (readPort_bijective hv v)).symm u) := by
    let p := (Equiv.ofBijective _ (readPort_bijective hv v)).symm u
    have hp : readPort hv p = u := (Equiv.ofBijective _ (readPort_bijective hv v)).apply_symm_apply u
    exact (congrArg (R.slot _) hp.symm).trans (readPort_spec hv p).1
  simp only [spec]
  unfold entry
  split
  next h =>
    have hh := code.injective h.choose_spec
    dsimp only
    rw [hh]
    split
    next hn =>
      apply congrArg (coefficient (z v))
      funext u
      apply congrArg x
      apply (M.num v).injective
      exact ((M.num v).apply_symm_apply ⟨_,hn u⟩).trans (Fin.ext (congrArg (fun i : Fin 4 => i.val) (num u)))
    next hn =>
      exact False.elim (hn fun u => (congrArg (fun i : Fin 4 => i.val) (num u)) ▸ (M.num v _).isLt)
  next h => exact False.elim (h ⟨_,rfl⟩)

/-- The code identifies accepted role assignments bijectively with the passing
bit decorations. -/
def acceptedEquiv :
    {z : V → RoleLabel T // R.Accepts M z} ≃
      {d : V → Bits h // (R.spec code coefficient).Valid (view M) d} :=
  Equiv.ofBijective
    (fun z => ⟨code ∘ z.val, (R.valid_encoded_iff code M coefficient z.val).mpr z.property⟩)
    ⟨by
        intro z y he
        apply Subtype.ext
        exact funext fun v => code.injective (congrFun (congrArg Subtype.val he) v),
     by
        intro d
        obtain ⟨z,⟨hz,ha⟩,_⟩ := (R.valid_iff code M coefficient d.val).mp d.property
        exact ⟨⟨z,ha⟩,Subtype.ext hz⟩⟩

@[simp] theorem acceptedEquiv_val (z : {z : V → RoleLabel T // R.Accepts M z}) :
    (R.acceptedEquiv code M coefficient z).val = code ∘ z.val := rfl

section Contraction

variable {A : Type*} [CommSemiring A]
    (C : (a : RoleLabel T) → (RolePort T a → Bits s) → A)

/-- Original, role-indexed contraction on an accepted replacement. -/
def roleContraction (z : {z : V → RoleLabel T // R.Accepts M z}) : A :=
  let hv := z.property.2.2.choose
  M.graph.contraction (A := fun _ => Bits s) (fun v x =>
    C (z.val v) (fun u => x ((Equiv.ofBijective _ (readPort_bijective hv v)).symm u)))

theorem decoratedContraction_role (z : {z : V → RoleLabel T // R.Accepts M z}) :
    (R.spec code C).decoratedContraction (view M) (code ∘ z.val) = R.roleContraction M C z := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro v _
  exact R.entry_at_role code M C z.val z.property.2.2.choose v _

/-- The functional of the compressed uniform tables sums the contractions
of exactly the accepted role-labelled replacements. -/
theorem Z_eq_accepted [Fintype (RoleLabel T)] (N : ℕ) :
    Z N (width s h) (R.spec code C).compiled =
      ∑ c : MapClass N, ∑ z : {z // R.Accepts c.out.map z}, R.roleContraction c.out.map C z := by
  rw [DecoratedMaps.Z_eq_sum_valid_classes, ← DecoratedMaps.Family.sum_valid_classes]
  apply Finset.sum_congr rfl
  intro c _
  symm
  apply Fintype.sum_equiv (R.acceptedEquiv code c.out.map C)
  intro z
  exact (R.decoratedContraction_role code c.out.map C z).symm

include code C in
/-- Isomorphisms transport the decoded roles by relabeling vertices, with
the same checked record, list position, role number and mark. -/
theorem accepts_iso {W D : Type*} [Fintype W] [Fintype D] [DecidableEq W]
    {H : RootedMap W D} (f : M.Iso H) (z : V → RoleLabel T) (z' : W → RoleLabel T)
    (he : ∀ v, z' (f.vertex v) = z v) :
    R.Accepts M z ↔ R.Accepts H z' := by
  rw [← R.valid_encoded_iff code M C, ← R.valid_encoded_iff code H C]
  exact (R.spec code C).valid_iso f _ _ (fun v => congrArg code (he v))

/-- The class family for the reverse construction has actual tree roles as
labels. Its transport preserves every underlying role name. -/
def acceptedFamily (N : ℕ) : DecoratedMaps.Family N where
  Label A := {z // R.Accepts A.map z}
  move {A B} f :=
    { toFun z := ⟨z.val ∘ f.vertex.symm, (R.accepts_iso code A.map C f z.val _ (by simp)).mp z.property⟩
      invFun z := ⟨z.val ∘ f.vertex, (R.accepts_iso code A.map C f _ z.val (fun _ => rfl)).mpr z.property⟩
      left_inv := fun z => Subtype.ext (by funext v; simp)
      right_inv := fun z => Subtype.ext (by funext v; simp) }
  move_refl _ _ := rfl
  move_trans _ _ _ := rfl

instance [Fintype (RoleLabel T)] (N : ℕ) (A : MapRep N) :
    Fintype ((R.acceptedFamily code C N).Label A) :=
  inferInstanceAs (Fintype {z // R.Accepts A.map z})

/-- Original tensor contraction as a function on accepted labelled map classes. -/
def acceptedWeight {N : ℕ} : (R.acceptedFamily code C N).Class → A :=
  Quotient.lift (fun x : (R.acceptedFamily code C N).Rep => R.roleContraction x.1.map C x.2) (by
    rintro a b ⟨f,hf⟩
    refine (R.decoratedContraction_role code a.1.map C a.2).symm.trans
      (((R.spec code C).decoratedContraction_iso f _ _ ?_).trans
        (R.decoratedContraction_role code b.1.map C b.2))
    intro v
    have := congrFun (congrArg Subtype.val hf) (f.vertex v)
    change (a.2.val ∘ f.vertex.symm) (f.vertex v) = b.2.val (f.vertex v) at this
    exact congrArg code (by simpa using this.symm))

theorem Z_eq_role_classes [Fintype (RoleLabel T)] (N : ℕ) :
    Z N (width s h) (R.spec code C).compiled =
      ∑ q : (R.acceptedFamily code C N).Class, R.acceptedWeight code C q := by
  rw [R.Z_eq_accepted code C, ← DecoratedMaps.Family.sum_valid_classes]
  rfl

end Contraction

/-- Hardwiring the catalogue's role and slot tests preserves the weight
bound of the original local tensor entries. -/
theorem tensor_hasFormula {F X : Type*} [Field F] {W : ℕ} (hW : 1 ≤ W)
    (C : (a : RoleLabel T) → (RolePort T a → Bits s) → MvPolynomial X F)
    (hC : ∀ a x, PlanarPatch.HasFormula W (C a x)) (θ : MapType) (d : Bits h)
    (x : Fin θ.degree.val → Bits s) : PlanarPatch.HasFormula W ((R.spec code C).tensor θ d x) := by
  change PlanarPatch.HasFormula W (R.entry code C θ d x)
  unfold entry
  split
  · dsimp only
    split
    · exact hC ..
    · simpa using (PlanarPatch.HasFormula.const (I := X) (0 : F)).mono hW
  · simpa using (PlanarPatch.HasFormula.const (I := X) (0 : F)).mono hW

end LocalRules
end PortGraph.ReplacementTemplate

end

end SpectralBooks
end LinearAlgebra
end OAI
