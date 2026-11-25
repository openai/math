import OAI.Computability.BorderVNP.TeamSiteChunkJoint

/-!
# Finite schedule uniqueness and soundness

At any positive processor count the complete finite array of charged blocks and
outgoing frames is uniquely determined by the path if the explicit capacities
suffice. Conversely, a successful array starting from the public live registers
recovers the locally accepting native path without a supplied native-run premise.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite

open VPVNP RAMTape BurstRAM RAMTape.PublicExprMachine TeamTapeHandoff TeamLocalClock

variable {w p r k a teams : ℕ}

/-- A complete finite-PC checked schedule from the public live state recovers its
native local accepting path, by concatenating checked rows across their shared
register frames. At least one row is required. -/
theorem ChargedRows.local_initial {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w}
    {lib : TeamOpcode.Macros w a} {H limit cap : Word w} {start : TeamOpcode.State w p r}
    {rows : List (List (TeamRAM.Event w))} {frames : List (Frame w r)}
    (hs : ChargedRows P pub lib H limit cap (initial (packed w start.pc.val) start.reg) rows frames)
    (fits : p ≤ 2^w) (ne : rows ≠ []) :
    TeamRAM.Local (P.fetch pub lib) start rows.flatten :=
  hs.local_live fits ne

private def array {α : Type*} (xs : List α) (size : xs.length = teams) (i : Fin teams) : α :=
  xs[i.val]'(size.symm ▸ i.isLt)

private theorem ofFn_array {α : Type*} (xs : List α) (size : xs.length = teams) :
    List.ofFn (array xs size) = xs := by
  apply List.ext_getElem (by simp [size])
  intro i h₁ h₂; simp [array]

/-- The exact finite hypotheses of the greedy decomposition suffice for one and only
one array of actual charged rows and outgoing frames. The final processor has the
canonical accepted status at the exact total tick count. -/
theorem existsUnique_schedule (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : TeamOpcode.Macros w a) (H limit cap : Word w) (fits : p ≤ 2^w) (hr : 0 < teams)
    (start : TeamOpcode.State w p r) (es : List (TeamRAM.Event w))
    (path : TeamRAM.Local (P.fetch pub lib) start es) (bound : ∀ e ∈ es, e.action.extra ≤ cap.val)
    (time : cost es ≤ limit.val) (capacity : cost es ≤ teams*(H.val-cap.val)) :
    ∃! rows : (Fin teams → List (TeamRAM.Event w)) × (Fin teams → Frame w r),
      (List.ofFn rows.1).flatten = es ∧
      ChargedRows P pub lib H limit cap (initial (packed w start.pc.val) start.reg) (List.ofFn rows.1) (List.ofFn rows.2) ∧
      (List.ofFn rows.2).getLast? = some (.accepted (packed w (cost es))) := by
  obtain ⟨bs,⟨hb,hf,hg⟩,hu⟩ := Team.existsUnique_teamBlocks (fun e : TeamRAM.Event w => e.action.extra)
    H.val cap.val teams es bound capacity
  let input := initial (packed w start.pc.val) start.reg
  let src := Model.wordFetch P pub lib
  have wordPath := (local_encode P pub lib fits start es).mpr path
  obtain ⟨fs,hc,hlen,hend⟩ := exists_chain src (Model.encode start) 0 limit input (Or.inl rfl)
    bs (hf ▸ wordPath) (by simpa only [hf, Fin.val_zero, Nat.zero_add] using time)
  have nonempty : bs ≠ [] := by rintro rfl; simp at hb; omega
  have hrow := (chargedRows_iff P pub lib H limit cap fits start bs fs (hf ▸ path)
    (fun e he => bound e (hf ▸ he)) (hf ▸ time)).mpr ⟨hg,hc⟩
  have hlast : fs.getLast? = some (.accepted (packed w (cost es))) := by simpa only [hf, Fin.val_zero, Nat.zero_add] using hend nonempty
  let rb := array bs hb
  let rf := array fs (hlen.trans hb)
  have eb : List.ofFn rb = bs := ofFn_array bs hb
  have ef : List.ofFn rf = fs := ofFn_array fs (hlen.trans hb)
  refine ⟨(rb,rf),?_,?_⟩
  · simpa only [eb,ef] using And.intro hf (And.intro hrow hlast)
  · rintro ⟨blocks,out⟩ ⟨flat,checked,_⟩
    obtain ⟨maximal, chain⟩ := checked.spec fits (fun e he => bound e (flat ▸ he))
    have eql := hu (List.ofFn blocks) ⟨List.length_ofFn,flat,maximal⟩
    rw [eql] at chain
    have eqf := chain_unique src limit chain hc
    exact Prod.ext (List.ofFn_injective (eql.trans eb.symm)) (List.ofFn_injective (eqf.trans ef.symm))

end TeamSite

end BorderVNP
end Computability
end OAI
