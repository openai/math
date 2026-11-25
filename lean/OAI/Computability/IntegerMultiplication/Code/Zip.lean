import OAI.Computability.IntegerMultiplication.Code.List

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code.Task
variable {X : Type*}

private def zipBody : Cmd :=
  splitRoot 1 (fun _ => splitRoot 0 (give 0) .pass) <|
    splitRoot 0 (fun _ => .pass) <|
      .join (move 1 0 2) <| .join (pack 0) <|
        .join (move 0 3 2) <| .join (.again 0) <|
          .join (move 3 0 2) (pack 0)

/-- Align two streams with possibly different shapes of records, but the same count.
Cost is just linear in sum of their volumes. -/
theorem zipTrees (f g : X → Tree) :
    Task (fun l : List X => (forest f l).count+(forest g l).count)
      (fun i => .fork (forest f i) (forest g i))
      (fun i => forest (fun x => .fork (f x) (g x)) i) := by
  let j := fun x => Tree.fork (f x) (g x)
  let b := zipBody
  let H := fun l => 150*((forest f l).count+(forest g l).count)
  refine ⟨splitRoot 0 (fun _ => .pass) ((move 0 1 2).join (.tie b)),200,fun l E r => ?_⟩
  suffices hc : Fits (b::E) b (pile 1 (forest f l) (pile 0 (forest g l) r))
      (pile 0 (forest j l) r) (H l) by
    beta_reduce
    refine (fits_pair ((fits_move (i:=0) (j:=1) (u:=2) (by decide) (by decide)
      (forest f l) E _).join hc.tie)).mono ?_
    simp only [H]
    omega
  induction l generalizing r with
  | nil => exact (fits_bit (b:=false) (fits_bit (b:=false) (fits_give false r _ _))).mono (by simp [H])
  | cons x l ih =>
    let env := b::E
    let z := pile 1 (forest f l) (pile 0 (forest g l) r)
    have h₁ := fits_move (i:=1) (j:=0) (u:=2) (by decide) (by decide) (f x) env
      (pile 0 (g x) z)
    have h₂ := fits_pack (f x) (g x) z 0 env
    have h₃ := fits_move (i:=0) (j:=3) (u:=2) (by decide) (by decide) (j x) env z
    have hi := ih (pile 3 (j x) r)
    rw [pile_comm 0 _ r 3 _ (by decide), pile_comm 1 _ _ 3 _ (by decide),
        pile_comm 0 (forest j l) _ _ _ (by decide)] at hi
    have h₄ := fits_move (i:=3) (j:=0) (u:=2) (by decide) (by decide) (j x) env (pile 0 (forest j l) r)
    have he := h₁.join (h₂.join (h₃.join ((Fits.again0 hi).join (h₄.join (fits_pack _ _ _ _ _)))))
    -- peel second list on 0
    dsimp only [z] at he
    rw [pile_comm 1 (f x) _ 0 (g x) (by decide),
        pile_comm 1 _ r 0 (forest g l) (by decide),
        pile_comm 1 _ _ 0 (forest g l) (by decide)] at he
    have he' := fits_pair (c := fun _ => .pass) he
    rw [pile_comm 0 (.fork ..) _ 1 _ (by decide),
        pile_comm 0 (.fork ..) r 1 _ (by decide)] at he'
    refine (fits_pair he').mono ?_
    simp only [H, Tree.count, j, forest_cons]
    omega

private def splitBody : Cmd :=
  -- return g stream on 0 and f stream on 1
  splitRoot 0 (fun _ => .join (give 0 false) (give 1 false))
  <| splitRoot 0 (fun _ => .pass) <|
    .join (move 0 4 2) <| -- left parked on 4
    .join (move 0 3 2) <| -- right parked on 3
    .join (.again 0) <|
      -- result lists on 0,1 (from recursion), above parked heads. Can't access f head on 1!
      -- need park f on separate fixed stack 4, not 1.
      .join (move 4 1 2) <| .join (move 3 0 2) <| .join (pack 1) (pack 0)

theorem unzipTrees (f g : X → Tree) :
    Task (fun l : List X => (forest (fun x => .fork (f x) (g x)) l).count)
      (fun l => forest (fun x => .fork (f x) (g x)) l)
      (fun l => .fork (forest f l) (forest g l)) := by
  let j := fun x => Tree.fork (f x) (g x)
  let b := splitBody
  refine ⟨(Prog.tie b).join ((move 1 0 2).join (pack 0)),190,fun l E r => ?_⟩
  change Fits _ _ (pile 0 (forest j l) r) _ (190*((forest j l).count+1))
  suffices hs : Fits (b::E) b (pile 0 (forest j l) r)
      (pile 1 (forest f l) (pile 0 (forest g l) r)) (125*(forest j l).count) by
    refine (hs.tie.join ((fits_move (i:=1) (j:=0) (u:=2) (by decide) (by decide)
      (forest f l) E _).join (fits_pack _ _ _ _ _))).mono ?_
    have hh : (forest f l).count ≤ (forest j l).count := by
      clear hs
      induction l with
      | nil => rfl
      | cons x l ih =>
        simp only [j,forest_cons,Tree.count]; dsimp only [j] at ih; omega
    omega
  let env := b::E
  induction l generalizing r with
  | nil =>
    have hu := (fits_give false r 0 env).join (fits_give false _ 1 env)
    refine (fits_bit (c := fun _ => _) (b:=false) hu).mono (by simp [Tree.count])
  | cons x l ih =>
    have h₁ := fits_move (i:=0) (j:=4) (u:=2) (by decide) (by decide) (f x) env
      (pile 0 (g x) (pile 0 (forest j l) r))
    have h₂ := fits_move (i:=0) (j:=3) (u:=2) (by decide) (by decide) (g x) env
      (pile 0 (forest j l) (pile 4 (f x) r))
    rw [pile_comm 4 _ _ 0 _ (by decide), pile_comm 4 _ r 0 _ (by decide)] at h₁
    rw [pile_comm 3 _ _ 0 _ (by decide)] at h₂
    have he := ih (pile 3 (g x) (pile 4 (f x) r))
    have h₃ := fits_move (i:=4) (j:=1) (u:=2) (by decide) (by decide) (f x) env
      (pile 1 (forest f l) (pile 0 (forest g l) (pile 3 (g x) r)))
    rw [pile_comm 4 _ _ 1 _ (by decide),
        pile_comm 4 _ _ 0 _ (by decide),
        pile_comm 4 _ r 3 _ (by decide)] at h₃
    have h₄ := fits_move (i:=3) (j:=0) (u:=2) (by decide) (by decide) (g x) env
      (pile 1 (f x) (pile 1 (forest f l) (pile 0 (forest g l) r)))
    -- commute input 3 past 1,1,0 and output 0 past 1,1
    rw [pile_comm 3 _ _ 1 _ (by decide), pile_comm 3 _ _ 1 _ (by decide),
      pile_comm 3 _ _ 0 _ (by decide), pile_comm 0 (g x) _ 1 _ (by decide),
      pile_comm 0 (g x) _ 1 _ (by decide)] at h₄
    have h₅ := fits_pack (f x) (forest f l) (pile 0 (g x) (pile 0 (forest g l) r)) 1 env
    have h₆ := fits_pack (g x) (forest g l) (pile 1 (Tree.fork (f x) (forest f l)) r) 0 env
    rw [pile_comm 0 (forest g l) r 1 _ (by decide), pile_comm 0 (g x) _ 1 _ (by decide),
        pile_comm 0 (.fork ..) r 1 _ (by decide)] at h₆
    have hc := h₁.join (h₂.join ((Fits.again0 he).join (h₃.join (h₄.join (h₅.join h₆)))))
    exact (fits_pair (fits_pair hc)).mono (by simp only [forest_cons,j,Tree.count]; omega)

end Code.Task

end IntegerMultiplication
end Computability
end OAI
