import OAI.Computability.BorderVNP.RoutingISACubeConstants
import OAI.Computability.BorderVNP.RoutingISAInverse
import OAI.Computability.BorderVNP.RoutingISATableEvents

/-! # Native installation of the cube lookup operands -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Constants

/-- Loading a static binary word uses only unsigned returning operations. -/
theorem literal_unsigned (ds : List Bool) : (literal ds).unsigned = true ∧
    (literal ds).withoutAccept = true := by
  induction ds with
  | nil => exact ⟨rfl,rfl⟩
  | cons b bs ih => cases b <;> simp [literal,Code.unsigned,Code.withoutAccept,ih.1,ih.2]

/-- Installing any fixed table takes only unsigned ordinary word instructions
and always uses the enclosing table's final continuation. -/
theorem atField_unsigned (field : VPVNP.BurstRAM.Word 8) (xs : List ℕ) :
    (atField field xs).unsigned = true ∧ (atField field xs).withoutAccept = true := by
  have loop : (emitWords xs).unsigned = true ∧ (emitWords xs).withoutAccept = true := by
    induction xs with
    | nil => exact ⟨rfl,rfl⟩
    | cons a as ih => simp [emitWords,emitWord,Code.unsigned,Code.withoutAccept,
        (literal_unsigned (digits a)).1,(literal_unsigned (digits a)).2,ih.1,ih.2]
  simpa only [atField,readFrame,Code.block,Code.unsigned,Code.withoutAccept,Bool.true_and] using loop

end RoutingISA.Constants

namespace RoutingISA.CubeConstants

open VPVNP.BurstRAM Cube Cube.Tally DiagonalTallyPacketEmit

variable {n b h K s w : ℕ}

/-- Four real frame pointers designate the fixed lookup constants. -/
def Fields (f : Frame) (base idBase : ℕ) (mem : ℕ → ℕ) : Prop :=
  mem (base+81)=f.zeroAddr ∧ mem (base+82)=f.oneAddr ∧ mem (base+79)=f.recipes ∧ mem (base+47)=idBase

private theorem after_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (field : Word 8) (xs : List ℕ) (p : ℕ) (old : ℕ → ℕ) (st : Bank w) (m : Memory w)
    (actual : readings m=old) (hf : readings pub 0+field.val<2^w) (hp : old (readings pub 0+field.val)=p)
    (hw : 1<2^w) (room : p+xs.length<2^w) (values : ∀ x∈xs,x<2^w) :
    BoundedRun pub mac (Constants.atField field xs) st m (Constants.atField field xs).slots
      (fun z ↦ z.mem=Constants.image p xs old) :=
  (Constants.atField_run pub mac st m field xs p hf (actual ▸ hp) hw room values).mono le_rfl
    (fun z hz ↦ by rwa [actual] at hz)

/-- All four constant arrays are produced by actual ordinary instructions at
the announced addresses. The complete cost is bounded by the size of this
fixed fragment, which depends only on the chosen cube identity. -/
theorem install_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (st : Bank w) (m : Memory w)
    (f : Frame) (idBase : ℕ) (id : TableEntry n b h K s → ℕ)
    (fit : Fits f w (readings pub 0) idBase id) (fields : Fields f (readings pub 0) idBase (readings m)) :
    BoundedRun pub mac (install id) st m (install id).slots (fun z ↦ z.mem=image f idBase id (readings m)) := by
  let base := readings pub 0
  let orig := readings m
  let m₀ := Constants.image f.zeroAddr [0] orig
  let m₁ := Constants.image f.oneAddr [1] m₀
  let mr := Constants.image f.recipes (recipes n b h K s) m₁
  obtain ⟨zAddr,oAddr,rAddr,iAddr⟩ := fields
  have fb : base+112 ≤ f.zeroAddr := fit.frame
  have zo := fit.zero
  have ore := fit.one
  have ri := fit.recipesRoom
  have iw := fit.idsRoom
  have hw : 1 < 2^w := by omega
  have frame₀ (j : ℕ) (hj : j ≤ 111) : m₀ (base+j)=orig (base+j) :=
    Constants.image_outside _ _ _ _ (.inl (by omega))
  have frame₁ (j : ℕ) (hj : j ≤ 111) : m₁ (base+j)=orig (base+j) :=
    (Constants.image_outside _ _ _ _ (.inl (by omega))).trans (frame₀ j hj)
  have frameR (j : ℕ) (hj : j ≤ 111) : mr (base+j)=orig (base+j) :=
    (Constants.image_outside _ _ _ _ (.inl (by omega))).trans (frame₁ j hj)
  have addr (j : Word 8) (h : j.val ≤ 111) : readings pub 0+j.val < 2^w := by change base+j.val<_; omega
  have h₀ := after_run pub mac 81 [0] f.zeroAddr orig st m rfl (addr _ (by decide)) zAddr hw
    (by simp; omega) (by simp)
  have h₁ (u : Bank w) (mu : Memory w) (hm : readings mu=m₀) :=
    after_run pub mac 82 [1] f.oneAddr m₀ u mu hm (addr _ (by decide)) ((frame₀ 82 (by decide)).trans oAddr)
      hw (by simp; omega) (by simpa using hw)
  have hr (u : Bank w) (mu : Memory w) (hm : readings mu=m₁) :=
    after_run pub mac 79 (recipes n b h K s) f.recipes m₁ u mu hm (addr _ (by decide))
      ((frame₁ 79 (by decide)).trans rAddr) hw (by omega) fit.recipeWords
  have hi (u : Bank w) (mu : Memory w) (hm : readings mu=mr) :=
    after_run pub mac 47 (ids id) idBase mr u mu hm (addr _ (by decide)) ((frameR 47 (by decide)).trans iAddr)
      hw iw fit.idWords
  exact h₀.seq (fun u mu hu ↦ (h₁ u mu hu).seq fun v mv hv ↦ (hr v mv hv).seq hi)

/-- The fixed initialization adds neither choices, signs, nor an early accept. -/
theorem install_unsigned (id : TableEntry n b h K s → ℕ) : (install id).unsigned=true ∧
    (install id).withoutAccept=true := by
  have t₀ := Constants.atField_unsigned 81 [0]
  have t₁ := Constants.atField_unsigned 82 [1]
  have tr := Constants.atField_unsigned 79 (recipes n b h K s)
  have ti := Constants.atField_unsigned 47 (ids id)
  simp only [install,Code.block,Code.unsigned,Code.withoutAccept,t₀.1,t₀.2,t₁.1,t₁.2,tr.1,tr.2,ti.1,ti.2,
    Bool.and_self,and_self]

end RoutingISA.CubeConstants

end BorderVNP
end Computability
end OAI
