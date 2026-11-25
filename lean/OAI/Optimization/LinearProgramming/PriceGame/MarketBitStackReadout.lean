import OAI.Optimization.LinearProgramming.PriceGame.MarketBitStackBridge

/-! Decode the canonical signed prices from a complete Bellman table. The input frame stores
the common denominator, the table, and the dummy vertex index. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace GridMachine
namespace Readout
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Potentials Quiver Table

abbrev Context := (ℕ × List Item) × ℕ
def contextCode := prodCode (prodCode Nat.bits valuesCode) Nat.bits

def lookup (xs : List Item) (i : ℕ) := (xs.drop i).headD zeroItem

def normalized (z : Context × ℕ) : ℚ :=
  let D := z.1.1.1
  let table := z.1.1.2
  mkRat ((lookup table z.1.2).1.1 - (lookup table z.2).1.1) D

/-- Two serialized list lookups, a signed subtraction, and reduction using the positive
common denominator produce the paper's dummy-minus-good price. -/
noncomputable def normalizedP : Procedure (prodCode contextCode Nat.bits) ratCode normalized := by
  let ctx := first contextCode Nat.bits
  let field := (first (prodCode Nat.bits valuesCode) Nat.bits).comp ctx
  let D := (first Nat.bits valuesCode).comp field
  let tab := (second Nat.bits valuesCode).comp field
  let dummy := (second (prodCode Nat.bits valuesCode) Nat.bits).comp ctx
  let good := second contextCode Nat.bits
  let score := (first intCode intCode).comp (first keyCode routeCode)
  let d := score.comp ((listGet itemCode zeroItem).comp (dummy.pair tab))
  let g := score.comp ((listGet itemCode zeroItem).comp (good.pair tab))
  exact (makeRat.comp ((intSub.comp (d.pair g)).pair D)).congrFun (fun _ => rfl)

noncomputable def pricesP : Procedure (prodCode (listCode Nat.bits) contextCode) (listCode ratCode)
    (fun z : List ℕ × Context => z.1.map (fun i => normalized (z.2,i))) :=
  mapWithContext (0 : ℕ) (0 : ℚ) normalizedP

variable {V : Type*} [Quiver V] {n : ℕ} (index : V ≃ Fin n)
variable (w : ∀ {a b : V}, (a ⟶ b) → ℚ) (r : V → ℚ) (ident : ∀ {a b : V}, (a ⟶ b) → ℕ)

theorem lookup_serialized (D : ℕ) (p : (v : V) → Plan w r v) (v : V) :
    lookup (serializeValues index w r ident D p) (index v).val = serializePlan w r ident D (p v) := by
  have hi : (index v).val < (List.finRange n).length := by simp
  have he : (List.finRange n)[(index v).val]? = some (index v) := by
    rw [List.getElem?_eq_getElem hi]
    simp only [List.getElem_finRange]
    exact congrArg some (Fin.ext rfl)
  simp only [lookup,serializeValues,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_map,
    he,Option.map_some,Option.getD_some]
  exact congrArg (fun u => serializePlan w r ident D (p u)) (index.symm_apply_apply v)

theorem normalized_exact (D : ℕ) (hd : 0 < D) (p : (v : V) → Plan w r v)
    (hg : ∀ v, NumberBounds.OnGrid D (p v).total) (dummy good : V) :
    normalized (((D,serializeValues index w r ident D p),(index dummy).val),(index good).val) =
      (p dummy).total-(p good).total := by
  simp only [normalized,lookup_serialized,serializePlan,Rat.mkRat_eq_div,Int.cast_sub,
    Grid.coordinate_cast (hg dummy),Grid.coordinate_cast (hg good)]
  exact (div_eq_iff (Nat.cast_ne_zero.mpr hd.ne')).2 (by ring)

theorem price_of_potential [Fintype V] [∀ i j : V, Fintype (i ⟶ j)] (D : ℕ) (hd : 0 < D)
    (edgegrid : ∀ {a b : V} (e : a ⟶ b), NumberBounds.OnGrid D (w e))
    (out : (a : V) → List (Σ b : V, a ⟶ b))
    (hout : ∀ {a b : V} (e : a ⟶ b), (⟨b,e⟩ : Σ z : V, a ⟶ z) ∈ out a)
    (dummy good : V) :
    let p := fun v => Layer.lookup index (plans index w 0 out (n-1)) v
    normalized (((D,serializeValues index w 0 ident D p),(index dummy).val),(index good).val) =
      potential w 0 dummy - potential w 0 good := by
  let p (v : V) := Layer.lookup index (plans index w 0 out (n-1)) v
  have hg (v : V) : NumberBounds.OnGrid D (p v).total := by
    rw [(p v).total_spec]
    simpa [NumberBounds.OnGrid] using weight_denominator w D edgegrid (p v).path
  have hn : Fintype.card V = n := (Fintype.card_congr index).trans (Fintype.card_fin _)
  have hp (v : V) : (p v).total = potential w 0 v := by
    simpa only [potential, hn, p] using plans_total_eq_value index w 0 out hout (n-1) v
  exact (normalized_exact index w 0 ident D hd p hg dummy good).trans (by rw [hp,hp])

end Readout
end GridMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
