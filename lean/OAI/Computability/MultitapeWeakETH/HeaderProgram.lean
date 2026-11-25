import OAI.Computability.MultitapeWeakETH.InitialHeader

/-! # Polynomial-time numeric reads of the entire initial graph memory -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.InitialIncidence

open VPVNP Compression CompressorRecords DescriptorSpace
open IntegerMultiplication Code Carry Staff Strip
open private chooseEq from OAI.Computability.MultitapeWeakETH.IncidenceProgram
open scoped Classical
noncomputable section

variable {I : Type} {ρ : Regime I}

/-- Selection among fixed, possibly input-dependent numeric fields. -/
theorem selectField {d : ℕ} (j : I → Fin d) (index : Figure ρ (fun i => (j i).val))
    {f : Fin d → I → ℕ} (fields : ∀ c, Figure ρ (f c)) : Figure ρ (fun i => f (j i) i) := by
  have scan (cs : List (Fin d)) : Figure ρ (fun i => if j i ∈ cs then f (j i) i else 0) := by
    induction cs with
    | nil => simpa using (Figure.natural (r:=ρ) 0)
    | cons c cs ih =>
      have h := chooseEq index (Figure.natural c.val) (fields c) ih
      convert h using 1
      funext i
      by_cases eq : j i = c
      · simp [eq]
      · simp [eq,show (j i).val ≠ c.val from fun q => eq (Fin.ext q)]
  simpa using scan (List.finRange d)

private theorem addressed {g r j c : I → ℕ} (a : ℕ) (hg : Realizes ρ g) (hr : Realizes ρ r)
    (hc : Figure ρ c) (hj : Figure ρ j) :
    Figure ρ (fun i => column a (g i) (r i) (Fin.ofNat 6 (c i)) (j i)) := by
  obtain ⟨word,data,eq⟩ := hj
  apply selectField (f:=fun t i => column a (g i) (r i) t (j i)) (fun i => Fin.ofNat 6 (c i)) (hc.modded (Figure.natural 6))
  intro t
  obtain ⟨read,prog,spec⟩ := column_program a t
  refine ⟨_,(Regime.Has.pair hg (Regime.Has.pair hr data)).thenDo prog,?_⟩
  intro i
  simpa only [Function.comp_apply,tally_length,eq] using spec (tally (g i),tally (r i),word i)

variable {a : ℕ} {g r w n x : I → ℕ} {L : I → Layout}

private theorem rowsFigure (hg : Realizes ρ g) (hr : Realizes ρ r) :
    Figure ρ (fun i => rows a (g i) (r i)) :=
  let V := ((Figure.natural 2).multiplied ((Figure.of_spoken hg).added
    ((Figure.of_spoken hr).added (Figure.natural 2)))).subtracted (Figure.natural 2)
  (((V.added (Figure.natural 2)).multiplied ((Figure.natural 2).repeated hg)).multiplied (Figure.natural _))

private theorem verticesFigure (hg : Realizes ρ g) (hr : Realizes ρ r) :
    Figure ρ (fun i => vertices (g i) (r i)) :=
  ((((Figure.natural 2).multiplied ((Figure.of_spoken hg).added
    ((Figure.of_spoken hr).added (Figure.natural 2)))).subtracted (Figure.natural 2)).added (Figure.natural 2))

/-- Evaluate the layout header scalars and then the incidence contents or
the inherited memory at an arbitrary address. Address arithmetic uses
ordinary binary magnitudes. Only the returned word is truncated. -/
theorem level_program (a : ℕ) (hg : Realizes ρ g) (hr : Realizes ρ r) (hw : Realizes ρ w)
    (hn : Figure ρ n) (hx : Figure ρ x) (m : ∀ i, BurstRAM.Memory (w i))
    (old : Figure ρ (fun i => (m i (x i)).val))
    (head : Figure ρ (fun i => levelStart (L i) 0))
    (start : Figure ρ (fun i => incidenceStart (L i) 0))
    (arena : Figure ρ (fun i => endAddress (L i)))
    (levels : Figure ρ (fun i => (L i).levels))
    (fields : Figure ρ (fun i => (L i).shape.scalarFields))
    (arrays : Figure ρ (fun i => arrayBase (L i) 0))
    (tableSize : Figure ρ (fun i => tableWords (L i))) :
    Figure ρ (fun i => (levelMemory (L i) a (g i) (r i) (n i) (m i) (x i)).val) := by
  let N := rowsFigure (a:=a) hg hr
  let idx := hx.subtracted head
  let diff := hx.subtracted start
  let row := diff.modded N
  let col := diff.quotients N
  let modulus := (Figure.natural 2).repeated hw
  let endCols := start.added ((Figure.natural 6).multiplied N)
  let six := Figure.natural (r:=ρ) 6
  let zero := Figure.natural (r:=ρ) 0
  have value (c : Fin 6) : Figure ρ (fun i => Scalars.values (.terminal a) (vertices (g i) (r i)) (g i) c) := by
    fin_cases c
    · exact verticesFigure hg hr
    · exact Figure.natural _
    · exact (Figure.natural 2).repeated hg
    · simpa [Scalars.values,Scalars.Pass.spent] using (Figure.natural 2).repeated hg
    · exact Figure.natural _
    · exact zero
  have scalar := selectField (fun i => Fin.ofNat 6 (x i-levelStart (L i) 0)) (idx.modded six) value
  let cf := fields.added six
  let colHead := start.added ((idx.subtracted fields).multiplied N)
  let tabHead := arrays.added ((idx.subtracted cf).multiplied tableSize)
  let rest := zero.variant (colHead.variant tabHead (idx.compare_ cf)) (idx.compare_ fields)
  let startup := chooseEq idx (Figure.natural 14) arena (chooseEq idx (Figure.natural 28) levels
    (chooseEq idx (Figure.natural 29) hn rest))
  have header : Figure ρ (fun i => headerValue (L i) a (g i) (r i) (n i) (x i-levelStart (L i) 0)) :=
    scalar.variant startup (idx.compare_ six)
  let hword := header.modded modulus
  let iword := (addressed a hg hr col row).modded modulus
  have solution := old.variant ((hword.variant (iword.variant old (hx.compare_ endCols)) (hx.compare_ start)))
    (hx.compare_ head)
  convert solution using 1
  funext i
  simp only [levelMemory,install]
  have order : levelStart (L i) 0 ≤ incidenceStart (L i) 0 := Nat.le_add_right ..
  split_ifs <;> first | rfl | omega

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork.InitialIncidence
