import OAI.Optimization.LinearProgramming.PriceGame.LearningPackedTests

/-! # Normalization of packed historical probe fields

The physical machine also accepts short arrays. The source interpretation `unpackProbe`
uses exactly the same default entries at missing addresses. Thus rewriting a history
through the normalization preserves all historical comparisons, even off the run path.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open Control States.Mass

private theorem tests_congr (e : PackedExpert) (p q : PackedProbe)
    (h : p.level = q.level) (hv : ∀ i ∈ e.tuple, priceAt p i = priceAt q i)
    (hh : ∀ k j, e.pivot = some (k,j) → ancestorAt p k j = ancestorAt q k j) :
    packedTests e p = packedTests e q := by
  unfold packedTests
  rw [h]
  split
  next =>
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i hi
    have ho : outsidePacked e p i = outsidePacked e q i := by
      cases he : e.pivot with
      | none => simp [outsidePacked,he,hv i hi]
      | some v => obtain ⟨k,j⟩ := v; simp [outsidePacked,he,hv i hi,hh k j he]
    rw [ho]
    apply congrArg (List.cons _)
    exact List.map_congr_left (fun j hj => by simp [pairPacked,hv i hi,hv j hj])
  next => rfl

/-- Pairwise comparisons do not inspect the raw assignments of the skeleton template. -/
@[simp] theorem packedTests_changeRaw (e : PackedExpert) (ps : PackedProbe) (raw : List ℚ) :
    packedTests {e with raw} ps = packedTests e ps := rfl

private theorem price_unpack {N} (p : PackedProbe) (i : Vertex N p.level) :
    priceAt p (vertexEquivFin N p.level i).val = (unpackProbe N p).prices i := by
  simp [priceAt,atAddress,unpackProbe,lookupTable,List.head?_drop,show (default : ℚ) = 0 from rfl]

private theorem ancestor_unpack {N} (p : PackedProbe) (k : ℕ) (j : Vertex N k) :
    ancestorAt p k (vertexEquivFin N k j).val = (unpackProbe N p).history k j := by
  simp [ancestorAt,atAddress,unpackProbe,unpackHistory,lookupTable,List.head?_drop,show (default : ℚ) = 0 from rfl]

theorem packedTests_correct_unpacked {N} (e : Expert N) (p : PackedProbe) :
    packedTests (packExpert e) p = (e.skeleton.testsAt (unpackProbe N p)).map packTest := by
  rw [← packedTests_correct]
  by_cases h : p.level = e.skeleton.level
  · obtain ⟨l,y,hist⟩ := p
    change l = e.skeleton.level at h; subst l
    let p : PackedProbe := ⟨e.skeleton.level,y,hist⟩
    let norm := packProbe (unpackProbe N p)
    apply tests_congr _ p norm rfl
    · intro i hi
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
      let v := e.skeleton.tuple j
      change priceAt p (vertexEquivFin N _ v).val = priceAt norm (vertexEquivFin N _ v).val
      exact (price_unpack (N := N) p v).trans
        ((congrFun (unpackProbe_pack_prices (unpackProbe N p)).symm v).trans
          (price_unpack (N := N) (packProbe (unpackProbe N p)) v).symm)
    · intro k j hj
      change e.skeleton.pivot.map _ = some (k,j) at hj
      cases hpi : e.skeleton.pivot with
      | none => simp [hpi] at hj
      | some pvt =>
        obtain ⟨l,v⟩ := pvt
        simp only [hpi,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hj
        obtain ⟨rfl,rfl⟩ := hj
        rw [ancestor_unpack (N := N) p l v]
        change (unpackProbe N p).history l v = ancestorAt (packProbe (unpackProbe N p)) l _
        simpa only [p,unpackProbe,ancestorAt,atAddress,packProbe,unpackHistory,lookupTable,List.headD_eq_head?_getD,
          List.head?_drop,show (default : ℚ) = 0 from rfl] using
          (unpackHistory_pack (l := (unpackProbe N p).level) (unpackProbe N p).history l.isLt v).symm
  · have hn : (packProbe (unpackProbe N p)).level ≠ (packExpert e).level := h
    have hp : p.level ≠ (packExpert e).level := h
    simp [packedTests,hp,hn]

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
