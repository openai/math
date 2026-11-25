import OAI.Computability.BorderVNP.FiniteProcessorRowValue
import OAI.Computability.BorderVNP.TeamSiteConsistencyEndpoints

/-! # Joining adaptive field products at the actual handoff frames -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP RAMTape BurstRAM TeamSite TeamSiteEvents TeamSiteConsistency TeamTapeHandoff
open RAMTape.PublicExprMachine TeamLocalClock
open scoped BigOperators Classical

variable {Q Γ : Type} {p r k a m g n d e w teams : ℕ} {F : Type*} [Field F] [Fintype F]

/-- Source field value of a processor block from its transmitted incoming state.
The halted branch reads no native events. -/
noncomputable def rowProduct (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w) (lib : Fin a → Macro Q Γ m g)
    (weights : Returns Q Γ F m a) (fuel : ℕ) (f : Frame w r) (es : List (TeamRAM.Event w)) : F :=
  match f with
  | .accepted _ => 1
  | .live word regs _ => if h : word.val < p then pathProduct P pub lib weights fuel ⟨⟨word.val,h⟩,regs⟩ es else 0

omit [Fintype F] in
theorem rowProduct_live (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w) (lib : Fin a → Macro Q Γ m g)
    (weights : Returns Q Γ F m a) (fuel : ℕ) (s : TeamOpcode.State w p r) (elapsed : Word w)
    (fits : p ≤ 2^w) (es : List (TeamRAM.Event w)) :
    rowProduct P pub lib weights fuel (.live (packed w s.pc.val) s.reg elapsed) es =
      pathProduct P pub lib weights fuel s es := by
  have he := packed_val (s.pc.isLt.trans_le fits)
  have hp : (packed w s.pc.val).val < p := by rw [he]; exact s.pc.isLt
  simp only [rowProduct,hp,dite_true]
  congr 1
  have eq : (⟨(packed w s.pc.val).val,hp⟩ : Fin p) = s.pc := Fin.ext he
  rw [eq]

/-- The physically checked leaf of any passing typed block, at its actual chosen
clock, is the adaptive field product from the received state. -/
theorem row_leaf (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (weights : Returns Q Γ F m a)
    (X : Processor.Row.Context P lib n d e w) (fuel clock : ℕ) (es : List (TeamRAM.Event w)) (out : Frame w r)
    (cert : EndpointRow P X.pub (macros lib fuel) X.block X.limit X.cap X.frame es out)
    (pass : X.guard out = true) (sorted : X.sorted es) (nonzero : (chunkSign (some false) es).isSome = true)
    (budget : X.cost (Processor.Row.nativeCost w m g fuel es) es ≤ clock) :
    (chunkBits es,rowProduct P X.pub lib weights fuel X.frame es) ∈ FieldReplay.leaves (code P lib weights)
      (FieldStack.productOutput (factor lib weights) terminal) clock (Processor.start,Fintype.equivFin F 1)
      (StackCompiler.labeledInput Layout.input X.raw) := by
  have here : (chunkBits es,rowProduct P X.pub lib weights fuel X.frame es) ∈ FieldReplay.leaves (code P lib weights)
      (FieldStack.productOutput (factor lib weights) terminal) (X.cost (Processor.Row.nativeCost w m g fuel es) es)
      (Processor.start,Fintype.equivFin F 1) (StackCompiler.labeledInput Layout.input X.raw) := by
    cases fr : X.frame with
    | accepted elapsed =>
      rw [fr] at cert
      obtain ⟨rfl,safe,rfl⟩ := cert
      exact halted_leaf P lib weights X fuel elapsed fr safe pass sorted
    | live word regs elapsed =>
      rw [fr] at cert
      obtain ⟨safe,pc,z,fin,rfl,ch,ending⟩ := cert
      let s : TeamOpcode.State w p r := ⟨pc,regs⟩
      rw [rowProduct_live P X.pub lib weights fuel s elapsed X.fits es]
      rcases ending with ⟨guard,rfl⟩ | ⟨guard,rfl⟩
      · exact live_leaf P lib weights X fuel s z elapsed fr safe es fin none ch
          (Or.inl ⟨rfl,congrArg Prod.fst guard⟩) pass sorted nonzero
      · exact live_leaf P lib weights X fuel s z elapsed fr safe es fin (some z.pc) ch
          (Or.inr ⟨rfl,congrArg Prod.fst guard⟩) pass sorted nonzero
  obtain ⟨t,ht,z,b,run,halt,val⟩ := (FieldReplay.mem_leaves_iff ..).mp here
  exact (FieldReplay.mem_leaves_iff ..).mpr ⟨t,ht.trans_le budget,z,b,run,halt,val⟩

omit [Fintype F] in
private theorem chunk_append (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w) (lib : Fin a → Macro Q Γ m g)
    (weights : Returns Q Γ F m a) (fuel : ℕ) {s z : TeamOpcode.State w p r} {c fin : Window w} {es : List (TeamRAM.Event w)}
    (ch : Chunk (P.fetch pub (macros lib fuel)) s c es z fin) (suffix : List (TeamRAM.Event w)) :
    pathProduct P pub lib weights fuel s (es++suffix) =
      pathProduct P pub lib weights fuel s es * pathProduct P pub lib weights fuel z suffix := by
  induction ch with
  | nil => simp [pathProduct,foldEvents]
  | cons _ adv _ _ _ ih =>
    simpa only [List.cons_append,pathProduct,foldEvents,adv,mul_assoc] using congrArg (eventWeight lib weights fuel _ _ * ·) ih

private theorem accepted_tail {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w} {lib : TeamOpcode.Macros w a}
    {H limit cap elapsed : Word w} {rows : List (List (TeamRAM.Event w))} {frames : List (Frame w r)}
    (check : EndpointRows P pub lib H limit cap (.accepted elapsed) rows frames) : rows.flatten = [] := by
  induction rows generalizing frames with
  | nil => rfl
  | cons es rows ih =>
    cases frames with
    | nil => exact check.elim
    | cons f fs =>
      obtain ⟨⟨rfl,_,rfl⟩,rest⟩ := check
      exact ih rest

omit [Fintype F] in
/-- Across all true incoming frames, multiplying the local field products is the
field product of the complete chronological event list on the original registers. -/
theorem product_rows (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w) (lib : Fin a → Macro Q Γ m g)
    (weights : Returns Q Γ F m a) (fuel : ℕ) (fits : p ≤ 2^w) (H limit cap : Word w)
    (start : TeamOpcode.State w p r) (blocks : Fin teams → List (TeamRAM.Event w)) (outs : Fin teams → Frame w r)
    (checked : EndpointRows P pub (macros lib fuel) H limit cap (initial (packed w start.pc.val) start.reg)
      (List.ofFn blocks) (List.ofFn outs)) :
    (∏ j : Fin teams, rowProduct P pub lib weights fuel (predecessor (initial (packed w start.pc.val) start.reg) outs j) (blocks j)) =
      pathProduct P pub lib weights fuel start (List.ofFn blocks).flatten := by
  have aux (N : ℕ) (first : Frame w r) (rows : Fin N → List (TeamRAM.Event w)) (fs ins : Fin N → Frame w r)
      (hd : ∀ j, j.val = 0 → ins j = first) (adj : ∀ i j, j.val = i.val+1 → ins j = fs i)
      (rowsOK : EndpointRows P pub (macros lib fuel) H limit cap first (List.ofFn rows) (List.ofFn fs))
      (firstFits : ∀ word regs elapsed, first = .live word regs elapsed → word.val < p) :
      (∏ j : Fin N, rowProduct P pub lib weights fuel (ins j) (rows j)) =
        rowProduct P pub lib weights fuel first (List.ofFn rows).flatten := by
    induction N generalizing first with
    | zero =>
      cases first with
      | accepted => simp [rowProduct]
      | live word regs elapsed => simp [rowProduct,firstFits word regs elapsed rfl,pathProduct,foldEvents]
    | succ N ih =>
      rw [List.ofFn_succ,List.ofFn_succ] at rowsOK
      obtain ⟨here,later⟩ := rowsOK
      have nextFits : ∀ word regs elapsed, fs 0 = .live word regs elapsed → word.val < p := by
        intro word regs elapsed outEq
        cases first with
        | accepted t =>
          have he := here.2.2
          rw [outEq] at he; contradiction
        | live word₀ regs₀ t =>
          obtain ⟨_,_,z,fin,_,_,he⟩ := here
          rcases he with ⟨_,h⟩ | ⟨_,h⟩
          · rw [outEq] at h; contradiction
          · rw [outEq] at h
            have eq := (Frame.live.inj h).1
            rw [eq,packed_val (z.pc.isLt.trans_le fits)]
            exact z.pc.isLt
      have sub := ih (fs 0) (fun j => rows j.succ) (fun j => fs j.succ) (fun j => ins j.succ)
        (fun j h => adj 0 j.succ (by simp [h])) (fun i j h => adj i.succ j.succ (by simp [h])) later nextFits
      rw [Fin.prod_univ_succ,hd 0 rfl,sub,List.ofFn_succ,List.flatten_cons]
      cases first with
      | accepted t =>
        obtain ⟨he,_,h⟩ := here
        simp [h,rowProduct]
      | live word regs elapsed =>
        obtain ⟨_,pc,z,fin,hword,ch,he⟩ := here
        rw [hword]
        let s : TeamOpcode.State w p r := ⟨pc,regs⟩
        rw [rowProduct_live P pub lib weights fuel s elapsed fits, rowProduct_live P pub lib weights fuel s elapsed fits,
          chunk_append P pub lib weights fuel ch]
        rcases he with ⟨_,h⟩ | ⟨_,h⟩
        · rw [h] at later ⊢
          simp [s,accepted_tail later,rowProduct,pathProduct,foldEvents]
        · rw [h,rowProduct_live P pub lib weights fuel z fin.elapsed fits]
  let first := initial (packed w start.pc.val) start.reg
  have frames := native_frame_checks first outs
  have hf : ∀ word regs elapsed, first = .live word regs elapsed → word.val < p := by
    intro word regs elapsed h
    have he := (Frame.live.inj h).1
    rw [← he,packed_val (start.pc.isLt.trans_le fits)]
    exact start.pc.isLt
  exact (aux teams first blocks outs (predecessor first outs) frames.initial frames.adjacent checked hf).trans
    (rowProduct_live P pub lib weights fuel start 0 fits _)

end FieldProcessor

end BorderVNP
end Computability
end OAI
