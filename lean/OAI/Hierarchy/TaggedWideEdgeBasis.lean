import OAI.Hierarchy.TaggedWideRows
import OAI.Hierarchy.TaggedWideReportGrouping

namespace OAI
/-! # Physical bit indices of the positive-stage tensor after all shorter banks close -/

noncomputable section
namespace Hierarchy.Tagged.WideStack
open TaggedShorterBudget ProtocolRAMReportedPorts
open scoped Classical BigOperators

variable {F T : Type*} [CommSemiring F] [Fintype T] {n : ℕ} (key : T ↪ ℕ×ℕ)
  (groups : T→ℕ) (raw : Fin n→ProtocolRAMEmit.Row) (positive : Fin n→Prop)
  (stage : Fin n→ℕ) (w m : ℕ)

set_option quotPrecheck false in
local notation "reported" => fun t:T => atScale positive stage (key t).1 raw
set_option quotPrecheck false in
local notation "occ" => Occ groups (fun t:T=>(key t).2) reported w m
set_option quotPrecheck false in
local notation "BankBit" => (o : occ) × Fin ((reported o.1 o.2.2.val).width)
set_option quotPrecheck false in
local notation "EdgeBit" => (i : {i : Fin n // positive i}) × Fin (raw i.val).width

private theorem bit_live {i : Fin n} {j b : ℕ}
    (hi : b < (atScale positive stage j raw i).width) :
    positive i ∧ stage i=j := by
  by_contra miss
  simp [atScale,miss] at hi

/-- The original edge and its absolute bit index. The exposed global site
and edge IDs are unchanged when inactive records of other stages are
masked, and such records contribute no bit to this map. -/
def edgeBit (p : BankBit) : EdgeBit :=
  let good := bit_live raw positive stage p.2.isLt
  ⟨⟨p.1.2.2.val,good.1⟩,⟨p.2.val,by simpa [atScale,good] using p.2.isLt⟩⟩

/-- Each live reported bit occurs exactly once among all shorter types.
Only the true owning stage must have room for its packed group number. -/
def edgeBits
    (cover : ∀ i,positive i → 0<(raw i).width →
      ∃t, key t=(stage i,widthIndex m ((raw i).width/(w:ℝ))) ∧ (raw i).group<groups t) :
    BankBit ≃ EdgeBit := Equiv.ofBijective (edgeBit key groups raw positive stage w m) (by
  constructor
  · rintro ⟨⟨s,g,⟨i,hi⟩⟩,a⟩ ⟨⟨t,h,⟨j,hj⟩⟩,b⟩ eqn
    have row : i=j := congrArg (fun z : EdgeBit=>z.1.val) eqn
    subst j
    have ga := bit_live raw positive stage a.isLt
    have gb := bit_live raw positive stage b.isLt
    have gs : (raw i).group=g.val ∧ widthIndex m ((raw i).width/(w:ℝ))=(key s).2 := by
      simpa [atScale,ga] using hi
    have gt : (raw i).group=h.val ∧ widthIndex m ((raw i).width/(w:ℝ))=(key t).2 := by
      simpa [atScale,gb] using hj
    obtain rfl := key.injective (Prod.ext (ga.2.symm.trans gb.2) (gs.2.symm.trans gt.2))
    obtain rfl := Fin.ext (gs.1.symm.trans gt.1)
    have same : a=b := Fin.ext (congrArg (fun z : EdgeBit=>z.2.val) eqn)
    subst b
    rfl
  · rintro ⟨⟨i,live⟩,b⟩
    obtain ⟨t,typeAt,inside⟩ := cover i live (Nat.zero_lt_of_lt b.isLt)
    let own : Fin (groups t) := ⟨(raw i).group,inside⟩
    have selected : positive i ∧ stage i=(key t).1 := ⟨live,(congrArg Prod.fst typeAt).symm⟩
    have cls : widthIndex m ((raw i).width/(w:ℝ))=(key t).2 := (congrArg Prod.snd typeAt).symm
    let r : InGroup (reported t) w m (key t).2 own.val :=
      ⟨i,rfl,by simpa [atScale,selected] using cls⟩
    let p : BankBit := ⟨⟨t,own,r⟩,⟨b.val,by simp [r,atScale,selected]⟩⟩
    exact ⟨p,rfl⟩)

/-- Sum over the genuine original edge coordinates, independently of the
relative enumeration of stages, payload buckets and local grouped rows. -/
theorem sum_edge_bits
    (cover : ∀ i,positive i → 0<(raw i).width →
      ∃t, key t=(stage i,widthIndex m ((raw i).width/(w:ℝ))) ∧ (raw i).group<groups t)
    (φ : (BankBit→Bool)→F) :
    (∑ x : BankBit→Bool, φ x) =
      ∑ e : EdgeBit→Bool, φ (e ∘ edgeBit key groups raw positive stage w m) := by
  let equiv := edgeBits key groups raw positive stage w m cover
  let relabel : (EdgeBit→Bool) ≃ (BankBit→Bool) :=
    Equiv.arrowCongr equiv.symm (Equiv.refl Bool)
  exact (relabel.sum_comp φ).symm

/-- Reassemble the single true `Fin (2^width)` bond on each positive
reported edge, in the original site's least-significant-bit convention. -/
theorem sum_edge_words
    (cover : ∀ i,positive i → 0<(raw i).width →
      ∃t, key t=(stage i,widthIndex m ((raw i).width/(w:ℝ))) ∧ (raw i).group<groups t)
    (φ : (BankBit→Bool)→F) :
    (∑ x : BankBit→Bool, φ x) =
      ∑ e : (i : {i : Fin n // positive i})→Fin (2^(raw i.val).width),
        φ (fun p=>let q := edgeBit key groups raw positive stage w m p
                  (e q.1).val.testBit q.2.val) := by
  rw [sum_edge_bits key groups raw positive stage w m cover]
  let E := {i : Fin n // positive i}
  let bits := fun i:E=>(raw i.val).width
  let flat : ((i:E)→Fin (2^(bits i))) ≃ (EdgeBit→Bool) :=
    (Equiv.piCongrRight (fun i:E=>Computability.VPVNP.RAMSerialization.wordBits (bits i))).trans
      (Equiv.piCurry (fun (i:E) (_:Fin (bits i))=>Bool)).symm
  let f (e : EdgeBit→Bool) := φ (e ∘ edgeBit key groups raw positive stage w m)
  calc
    _ = ∑ e,f (flat e) := (flat.sum_comp f).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      apply congrArg φ
      funext p
      let q := edgeBit key groups raw positive stage w m p
      exact (Computability.VPVNP.LiveHeader.testBit_wordBits (e q.1) q.2).symm

end Hierarchy.Tagged.WideStack

end
end OAI
