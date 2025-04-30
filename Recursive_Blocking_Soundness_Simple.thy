theory Recursive_Blocking_Soundness_Simple
  imports Main Graph_Theory_Simple HOL.Wellfounded
begin

(* ------------------------------------------------------------------------- *)
subsection ‹Basic predicates used only by the recursive-blocking theory›
(* ------------------------------------------------------------------------- *)

consts
  Coll        :: "node ⇒ path ⇒ bool"          ― ‹v is collider on p›
  NonC        :: "node ⇒ path ⇒ bool"          ― ‹v is non-collider on p›
  Endpoint    :: "node ⇒ path ⇒ bool"
  OnPath      :: "node ⇒ path ⇒ bool"
  AfterOnPath :: "node ⇒ node ⇒ path ⇒ bool"
  Halts       :: "node set ⇒ bool"
  Growsto     :: "node set ⇒ node set ⇒ bool"
  StrictSubset:: "node set ⇒ node set ⇒ bool"
  Initial     :: "node set"
  Adj         :: "node ⇒ node ⇒ bool"

(* Dummy constants used in some axioms ------------------------------------- *)
consts
  V  :: "node set"
  b1 :: "node set"

(* ------------------------------------------------------------------------- *)
subsection ‹Path-blocking definitions (unchanged)›
(* ------------------------------------------------------------------------- *)

definition HasNC :: "path ⇒ node set ⇒ bool" where
  "HasNC p f ≡ ∃x. NonC x p ∧ x ∉ f"

definition NoAfterInB :: "node ⇒ node set ⇒ path ⇒ bool" where
  "NoAfterInB v b p ≡ ∀d. AfterOnPath d v p ⟶ d ∉ b"

definition DirectedPath :: "node ⇒ node ⇒ node list ⇒ bool" where
  "DirectedPath x y p ≡
      p ≠ [] ∧ hd p = x ∧ last p = y ∧
      (∀i < length p - 1. Adj (p ! i) (p ! (i + 1)))"

definition Desc :: "node ⇒ node ⇒ bool" where
  "Desc x y ≡ (∃p. DirectedPath x y p)"

definition NoDescInB :: "node ⇒ node set ⇒ bool" where
  "NoDescInB c B ≡ ¬ (∃d. Desc c d ∧ d ∈ B)"

definition Blocked where
  "Blocked p B ≡ (∃v. NonC v p ∧ v ∈ B) ∨ (∀c. Coll c p ⟶ NoDescInB c B)"

definition Unblocked :: "path ⇒ node set ⇒ bool" where
  "Unblocked p b ≡ ¬ Blocked p b"

definition MSep :: "node ⇒ node ⇒ node set ⇒ bool" where
  "MSep x y B ≡ ¬ Adj x y ∧ (∀p. Blocked p B)"

definition Path :: "node ⇒ node ⇒ path ⇒ bool" where
  "Path x y p ⟷ hd p = x ∧ last p = y ∧ walk p"

definition walk_p :: "node list ⇒ bool" where
  "walk_p p ≡ walk p"

definition ValidBlock :: "node set ⇒ bool" where
  "ValidBlock B ≡ (∀p c. Coll c p ⟶ NoDescInB c B)"

definition eligible_noncollider
  :: "node ⇒ node ⇒ node ⇒ node set ⇒ path ⇒ bool"
     ("Eligible'_noncollider _ _ _ _ _" [100,100,100,100,100] 100)
where
  "eligible_noncollider x y v B p ≡
        Unblocked p B
      ∧ Path x y p
      ∧ NonC v p
      ∧ v ∉ B
      ∧ (∀w. NonC w p ∧ w ∉ B ⟶ AfterOnPath w v p)"

definition NextB :: "node set ⇒ node ⇒ node set"  where
  "NextB B0 v ≡ B0 ∪ {v}"

(* ------------------------------------------------------------------------- *)
subsection ‹Three-way disjunction eliminator (helper lemma)›
(* ------------------------------------------------------------------------- *)

inductive Algorithm_steps
    :: "('g) ⇒ node ⇒ node ⇒ 'c ⇒ 'f ⇒ node set ⇒ bool"
where
  base:
    "Initial_B graph x y C F = B      ⟹
     Algorithm_steps graph x y C F B"                   ― ‹no step needed›
| step:
    "RB_step      graph x y C F B0 B1 ⟹
     Algorithm_steps graph x y C F B1 ⟹
     Algorithm_steps graph x y C F B0"

inductive RB_step
  :: "('g) ⇒ node ⇒ node ⇒ 'c ⇒ 'f ⇒ node set ⇒ node set ⇒ bool"
where
  add_noncollider:
    "eligible_noncollider x y v B0 p ⟹
     RB_step g x y C F B0 (NextB B0 v)"

lemma disjE3:
  assumes "A ∨ B ∨ C"
    and AB: "A ⟹ R" and BB: "B ⟹ R" and CB: "C ⟹ R"
  shows R
  using assms by blast

lemma elig_not_collider:
  "eligible_noncollider x y v B p ⟹ ¬ Coll v p"
  sorry
  (*by (auto simp: eligible_noncollider_def)*)

lemma elig_not_desc_of_collider:
  assumes E: "eligible_noncollider x y v B p"
      and C: "Coll c p"
      and A: "AfterOnPath v c p"
    shows "¬ Desc c v"
  sorry
  (*using E C A by (auto simp: eligible_noncollider_def)*)


lemma extend_preserves_ValidBlock:
  assumes step:  "RB_step graph x y C F B0 B1"       ― ‹one loop iteration›
      and inv0:  "ValidBlock B0"
    shows   "ValidBlock B1"
  sorry

lemma algorithm_preserves_invariant:
  assumes run: "Algorithm_steps graph x y C F B"
  shows   "ValidBlock B"
  sorry

(* ------------------------------------------------------------------------- *)
subsection ‹High-level soundness›
(* ------------------------------------------------------------------------- *)

lemma fixpoint:
  assumes halts : "Halts B"
      and algo  : "Algorithm_steps graph x y C F B"
      and path  : "Path x y p"
  shows "Blocked p B"
proof (rule ccontr)
  ― ‹assume the opposite and derive a contradiction›
  assume nb: "¬ Blocked p B"

  ― ‹loop-invariant available after the run›
  have valid: "ValidBlock B"
    using algo by (rule algorithm_preserves_invariant)

  ― ‹from  ¬Blocked  pick a collider whose descendant is in B›
  obtain c where coll: "Coll c p" and bad: "¬ NoDescInB c B"
    using nb unfolding Blocked_def by (auto simp: not_all)

  ― ‹but the invariant says every collider satisfies NoDescInB›
  from valid coll have good: "NoDescInB c B"
    unfolding ValidBlock_def by blast

  ― ‹contradiction›
  from good bad show False by contradiction
qed

(* If we add one variable at a time to the blocking set, never removing
any,  and there is only a finite set of variables, the procedure must halt. *)
lemma termination_lemma:
  fixes V :: "'a set"
    and Halts :: "'a set ⇒ bool"
  assumes finV: "finite V"
    and init: "B ⊆ V"
    and grow: "⋀B. B ⊆ V ⟹ ¬ Halts B ⟹ (∃B'. B ⊂ B' ∧ B' ⊆ V)"
  shows "∃B. Halts B"
  sorry
(*proof (rule ccontr)
  assume no_halt: "¬ (∃B. Halts B)"

  text ‹Define the set of all subsets of V where Halts does not hold›
  let ?X = "{B. B ⊆ V ∧ ¬ Halts B}"
  let ?R = "{(x, y). x ⊂ y ∧ y ∈ ?X}"

  have finX: "finite ?X"
    using finV by (simp add: finite_subset)

  text ‹Every B ∈ ?X can be extended to a strictly larger B' in ?X›
  have no_max: "∀B ∈ ?X. ∃B'. B' ∈ ?X ∧ B ⊂ B'"
  proof
    fix B assume B_in: "B ∈ ?X"
    then have B_subV: "B ⊆ V" and nh: "¬ Halts B" by auto
    obtain B' where sub: "B ⊂ B'" and subV: "B' ⊆ V" and nh': "¬ Halts B'"
      using grow[OF B_subV nh] by blast
    then have "B' ∈ ?X" by (simp add: subV nh')
    then show "∃B'. B' ∈ ?X ∧ B ⊂ B'" using sub by blast
  qed

  text ‹But a finite set of subsets of a finite set cannot have an infinite ⊂-chain›
  have wf_subset: "wf ?R"
    using finX by (rule wf_finite_psubset)

  have "?X ≠ {}"
    using init no_halt by auto

  then obtain B where B_in: "B ∈ ?X"
    and min: "⋀B'. (B', B) ∈ ?R ⟹ B' ∉ ?X"
    using wf_subset by (rule wfE_min)

  have "Halts B"
    using min by auto

  then show False
    using no_halt by blast
qed*)


definition Weakly_minimal :: "node ⇒ node ⇒ node set ⇒ bool" where
  "Weakly_minimal x y B ≡
       (∀p. Path x y p ⟶ Blocked p B)        
     ∧ (∀v. v ∈ B ⟶
            (∃p. Path x y p ∧ NonC v p ∧
                 ¬ Blocked p (B - {v})))"  

(* ---------------------------------------------------------------- *)
subsection ‹Two auxiliary lemmas used in the minimality proof›
(* ---------------------------------------------------------------- *)

text ‹If a step adds exactly @{term v}, removing @{term v} from the new
      blocking set gives back the old set, so the witness path @{term p}
      is still unblocked.›
lemma path_is_blocked_after_halting:
  assumes halts : "Halts B"
      and run   : "Algorithm_steps g x y C F B"
      and path  : "Path x y p"
  shows  "Blocked p B"
proof (rule ccontr)
  assume nb: "¬ Blocked p B"          ― ‹assume p were still open›

  ― ‹loop invariant obtained from the full run›
  have valid: "ValidBlock B"
    using run by (rule algorithm_preserves_invariant)

  ― ‹from  ¬Blocked extract a collider that violates NoDescInB›
  obtain c where coll: "Coll c p" and bad: "¬ NoDescInB c B"
    using nb unfolding Blocked_def by (auto simp: not_all)

  ― ‹invariant says every collider already satisfies NoDescInB›
  from valid coll have good: "NoDescInB c B"
    unfolding ValidBlock_def by blast

  ― ‹contradiction›
  from good bad show False
    by contradiction
qed

lemma witness_persists:
  assumes step: "RB_step g x y C F B0 B1"
      and upd : "B1 = B0 ∪ {v}"
      and elig: "eligible_noncollider x y v B0 p"
  shows "¬ Blocked p (B1 - {v})"
proof -
  have "v ∉ B0"
    using elig unfolding eligible_noncollider_def by auto
  hence "B1 - {v} = B0"
    using upd by auto
  moreover have "Unblocked p B0"
    using elig unfolding eligible_noncollider_def by auto
  ultimately show ?thesis
    unfolding Unblocked_def by simp
qed


text ‹Locate the \emph{last} step of the big run that inserted a given
      vertex @{term v}.  This supplies the predecessor set @{term B0}
      and the witness path @{term p}.›
lemma final_member_obtains_step:
  assumes run : "Algorithm_steps g x y C F B"
      and mem : "v ∈ B"
  obtains B0 p where
        "Algorithm_steps g x y C F B0"
      and "RB_step g x y C F B0 B"
      and "B = B0 ∪ {v}"
      and "eligible_noncollider x y  v B0 p"
  sorry
(*proof -
  ― ‹Step 1: locate predecessor set B0 and the RB_step that inserts v›
  obtain B0 where
    run0: "Algorithm_steps g x y C F B0" and
    stp : "RB_step g x y C F B0 B"       and
    upd : "B = B0 ∪ {v}"
    sorry
  proof -
    from run mem
    show ?thesis
    proof (induction rule: Algorithm_steps.induct)
      case base
      then show ?case by auto                     ― ‹v not in initial B›
    next
      case (step B0 B1)
      note IH    = step.IH
      note small = step.hyps(1)          ― ‹RB_step … B0 B1›
      note rest  = step.hyps(2)          ― ‹Algorithm_steps … B1›
      show ?case
      proof (cases "v ∈ B1")
        case in_B1                            ― ‹v already present›
        from IH[OF in_B1] show ?thesis by blast
      next
        case added_now                        ― ‹v added now›
        have "B = B1 ∪ {v}"
          using small added_now
          unfolding RB_step.simps NextB_def by auto
        moreover have "RB_step g x y C F B1 B"
          using small rest by (meson Algorithm_steps.step)
        ultimately show ?thesis
          using rest that by blast
      qed
    qed
  qed

  ― ‹Step 2: open that RB_step and recover its witness path p›
  obtain p where
    elig: "eligible_noncollider v B0 p"
    by (cases stp) (auto simp: RB_step.simps)

  ― ‹Deliver the four witnesses›
  show thesis
    using run0 stp upd elig that by blast
  qed
  
    ― ‹Step 2: open that RB_step and recover its witness path p›
    obtain p where
      elig: "eligible_noncollider v B0 p"
      by (cases stp) (auto simp: RB_step.simps)
  
    ― ‹Deliver the four witnesses›
    show thesis
      using run0 stp upd elig that by blast
  qed

  ― ‹Step 2: extract the witness path p from that RB_step›
  obtain p where
    elig: "eligible_noncollider v B0 p"
  proof -
    from stp obtain u q
      where stp_form: "stp = RB_step.add_noncollider g x y C F B0 (NextB B0 u)"
        and "u = v" and "elig: eligible_noncollider v B0 q"
      by (cases stp) auto
    thus ?thesis
      using that by blast
  qed

  ― ‹Deliver the four witnesses›
  show thesis
    using run0 stp upd elig that by blast
qed

  ― ‹Step 2:  open that small step to reveal its witness path p.›
  from stp obtain p
    where elig: "eligible_noncollider v B0 p"
    by (cases stp) (auto simp: RB_step.simps)

  ― ‹Deliver the four required witnesses.›
  show thesis
    using run0 stp upd elig that by blast
qed

  ― ‹–––– 2.  open that RB_step to obtain its witness path p –––––›
  obtain p where
    elig: "eligible_noncollider v B0 p"
    by (cases step) (auto simp: RB_step.simps)

  ― ‹assemble the desired 4-tuple of facts for the caller›
  show ?thesis
    using run0 step upd elig that by blast
qed*)


(* ---------------------------------------------------------------- *)
subsection ‹Weak-minimality of the final blocking set›
(* ---------------------------------------------------------------- *)

lemma blocking_set_weakly_minimal:
  assumes halts : "Halts B"
      and run   : "Algorithm_steps g x y C F B"
    shows   "Weakly_minimal x y B"
  sorry
(*proof -
  ― ‹(1) fixpoint: every path is blocked›
  have cover: "∀p. Path x y p ⟶ Blocked p B"
  proof
    fix p
    show "Path x y p ⟶ Blocked p B"
    proof
      assume Pp: "Path x y p"
      from halts run Pp
      show "Blocked p B"
        by (rule path_is_blocked_after_halting)
    qed
  qed

  ― ‹(2) indispensability: each v ∈ B keeps some path closed›
  have indispens:
    "∀v. v ∈ B ⟶ (∃p. Path x y p ∧ NonC v p ∧ ¬ Blocked p (B - {v}))"
  proof
    fix v assume "v ∈ B"
    ― ‹split the big run at the step that inserted v›
    obtain B0 p where
        run0:  "Algorithm_steps g x y C F B0"
      and step: "RB_step g x y C F B0 B"
      and upd:  "B = B0 ∪ {v}"
      and elig: "eligible_noncollider v B0 p"
      using final_member_obtains_step[OF run ‹v ∈ B›] by blast

    have nb: "¬ Blocked p (B - {v})"
      using witness_persists[OF step upd elig] .

    moreover
    have "Path x y p" and "NonC v p"
      using elig unfolding eligible_noncollider_def by auto
    ultimately
    show "∃p. Path x y p ∧ NonC v p ∧ ¬ Blocked p (B - {v})"
      by blast
  qed

  ― ‹combine (1) and (2)›
  show "Weakly_minimal x y B"
    unfolding Weakly_minimal_def
    using cover indispens by blast
qed*)

end