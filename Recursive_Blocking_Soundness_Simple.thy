theory Recursive_Blocking_Soundness_Simple
  imports Main Graph_Theory_Simple HOL.Wellfounded
begin



(* Dummy constants used in some axioms ------------------------------------- *)
consts
  V  :: "node set"
  b1 :: "node set"

consts Initial_B :: "graph ⇒ node ⇒ node ⇒ 'c ⇒ 'f ⇒ node set"

(* ------------------------------------------------------------------------- *)
subsection ‹Path-blocking definitions (unchanged)›
(* ------------------------------------------------------------------------- *)

definition HasNC :: "path ⇒ node set ⇒ bool" where
  "HasNC p f ≡ ∃x. NonC x p ∧ x ∉ f"

definition NoAfterInB :: "node ⇒ node set ⇒ path ⇒ bool" where
  "NoAfterInB v b p ≡ ∀d. AfterOnPath d v p ⟶ d ∉ b"

definition DirectedPath :: "graph ⇒ node ⇒ node ⇒ node list ⇒ bool" where
  "DirectedPath g x y p ≡
      p ≠ [] ∧ hd p = x ∧ last p = y ∧
      (∀i < length p - 1. Adj g (p ! i) (p ! (i + 1)))"

definition Desc :: "graph ⇒ node ⇒ node ⇒ bool" where
  "Desc g x y ≡ (∃p. DirectedPath g x y p)"

definition NoDescInB :: "graph ⇒ node ⇒ node set ⇒ bool" where
  "NoDescInB g c B ≡ ¬ (∃d. Desc g c d ∧ d ∈ B)"

definition Blocked :: "graph ⇒ path ⇒ node set ⇒ bool" where
  "Blocked g p B ≡ (∃v. NonC v p ∧ v ∈ B) ∨ (∀c. Coll c p ⟶ NoDescInB g c B)"

definition Unblocked :: "graph ⇒ path ⇒ node set ⇒ bool" where
  "Unblocked g p b ≡ ¬ Blocked g p b"

definition MSep :: "graph ⇒ node ⇒ node ⇒ node set ⇒ bool" where
  "MSep g x y B ≡ ¬ Adj g x y ∧ (∀p. Blocked g p B)"

definition Path :: "graph ⇒ node ⇒ node ⇒ path ⇒ bool" where
  "Path g x y p ⟷ hd p = x ∧ last p = y ∧ walk g p"

definition walk_p :: "graph ⇒ node list ⇒ bool" where
  "walk_p g p ≡ walk g p"

definition ValidBlock :: "graph ⇒ node set ⇒ bool" where
  "ValidBlock g B ≡ (∀p c. Coll c p ⟶ NoDescInB g c B)"

definition eligible_noncollider
  :: "graph ⇒ node ⇒ node ⇒ node ⇒ node set ⇒ path ⇒ bool"
     ("Eligible'_noncollider _ _ _ _ _ _" [100,100,100,100,100,100] 100)
where
  "eligible_noncollider g x y v B p ≡
        Unblocked g p B
      ∧ Path g x y p
      ∧ NonC v p
      ∧ v ∉ B
      ∧ (∀w. NonC w p ∧ w ∉ B ⟶ AfterOnPath w v p)"

definition NextB :: "node set ⇒ node ⇒ node set"  where
  "NextB B0 v ≡ B0 ∪ {v}"

(* ------------------------------------------------------------------------- *)
subsection ‹Three-way disjunction eliminator (helper lemma)›
(* ------------------------------------------------------------------------- *)

inductive RB_step
  :: "graph ⇒ node ⇒ node ⇒ 'c ⇒ 'f ⇒ node set ⇒ node set ⇒ bool"
where
  add_noncollider:
    "eligible_noncollider g x y v B0 p ⟹
     RB_step g x y C F B0 (NextB B0 v)"

inductive Algorithm_steps
    :: "graph ⇒ node ⇒ node ⇒ 'c ⇒ 'f ⇒ node set ⇒ bool"
where
  base:
    "Initial_B g x y C F = B ⟹
     Algorithm_steps g x y C F B"
| step:
    "RB_step g x y C F B0 B1 ⟹
     Algorithm_steps g x y C F B1 ⟹
     Algorithm_steps g x y C F B0"

lemma disjE3:
  assumes "A ∨ B ∨ C"
    and AB: "A ⟹ R" and BB: "B ⟹ R" and CB: "C ⟹ R"
  shows R
  using assms by blast

lemma elig_not_collider:
  "eligible_noncollider g x y v B p ⟹ ¬ Coll v p"
  sorry
  (* by (auto simp: eligible_noncollider_def) *)

lemma elig_not_desc_of_collider:
  assumes E: "eligible_noncollider g x y v B p"
      and C: "Coll c p"
      and A: "AfterOnPath v c p"
    shows "¬ Desc g c v"
  sorry
  (* using E C A by (auto simp: eligible_noncollider_def) *)


lemma extend_preserves_ValidBlock:
  assumes step: "RB_step g x y C F B0 B1"       ― ‹one loop iteration›
      and inv0: "ValidBlock g B0"
  shows   "ValidBlock g B1"
  sorry

lemma InitialBlock_is_valid:
  shows "∀g x y C F. ValidBlock g (Initial_B g x y C F)"
  sorry

lemma algorithm_preserves_invariant:
  assumes run: "Algorithm_steps g x y C F B"
  shows   "ValidBlock g B"
  using run
  sorry
(*proof (induction g x y C F B rule: Algorithm_steps.induct)
  case (base g x y C F B)
  ― ‹Given: Initial_B g x y C F = B›
  then show "ValidBlock g B"
    using InitialBlock_is_valid
    by (simp add: base.hyps)
next
  case (step g x y C F B0 B1)
  ― ‹Given: RB_step g x y C F B0 B1 and Algorithm_steps g x y C F B1›
  ― ‹IH: ValidBlock g B1›
  have rb: "RB_step g x y C F B0 B1" using step.hyps(1) .
  have IH: "ValidBlock g B1" using step.IH .
  show "ValidBlock g B0"
    using extend_preserves_ValidBlock[OF rb IH] .
qed*)

(* ------------------------------------------------------------------------- *)
subsection ‹High-level soundness›
(* ------------------------------------------------------------------------- *)

lemma fixpoint:
  assumes halts : "Halts B"
      and algo  : "Algorithm_steps g x y C F B"
  shows "∀p. Path g x y p ⟶ Blocked g p B"
proof
  fix p
  show "Path g x y p ⟶ Blocked g p B"
  proof
    assume path: "Path g x y p"
    show "Blocked g p B"
    proof (rule ccontr)
      assume nb: "¬ Blocked g p B"

      have valid: "ValidBlock g B"
        using algo by (rule algorithm_preserves_invariant)

      obtain c where coll: "Coll c p" and bad: "¬ NoDescInB g c B"
        using nb unfolding Blocked_def by (auto simp: not_all)

      from valid coll have good: "NoDescInB g c B"
        unfolding ValidBlock_def by blast

      from good bad show False by contradiction
    qed
  qed
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
proof (rule ccontr)
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
qed


definition Weakly_minimal :: "graph ⇒ node ⇒ node ⇒ node set ⇒ bool" where
  "Weakly_minimal g x y B ≡
       (∀p. Path g x y p ⟶ Blocked g p B)        
     ∧ (∀v ∈ B. ∃p. Path g x y p ∧ ¬ Blocked g p (B - {v}))"  

text ‹
  Invariant: Every node in B was added to block some path p that remains unblocked
  if v is removed from B. That is, B contains only “justified” nodes.

  This ensures weak minimality: no v ∈ B can be removed without reopening
  at least one x–y path.
›
definition JustifiedBlock :: "graph ⇒ node ⇒ node ⇒ node set ⇒ bool" where
  "JustifiedBlock g x y B ≡
     (∀v ∈ B. ∃p. Path g x y p ∧ v ∈ set p ∧ ¬ Blocked g p (B - {v}))"

lemma algorithm_ensures_justified_block:
  assumes "Algorithm_steps G x y C F B"
  shows "JustifiedBlock G x y B"
  sorry

lemma algorithm_inserts_only_necessary_nodes:
  assumes steps: "Algorithm_steps g x y C F B"
      and v_in_B: "v ∈ B"
  shows "∃p. Path g x y p ∧ ¬ Blocked g p (B - {v})"
  sorry

lemma weakly_minimal:
  assumes halt: "Halts B"
      and steps: "Algorithm_steps g x y C F B"
  shows "Weakly_minimal g x y B"
proof -
  ― ‹Part 1: Fixpoint — all paths are blocked›
  have all_blocked: "∀p. Path g x y p ⟶ Blocked g p B" 
    using halt steps by (rule fixpoint)

  ― ‹Part 2: Justification — every v in B is needed›
  have justified: "∀v ∈ B. ∃p. Path g x y p ∧ ¬ Blocked g p (B - {v})"
  proof
    fix v assume vB: "v ∈ B"
    from steps have "JustifiedBlock g x y B"
      using algorithm_ensures_justified_block by blast
    then obtain p where "Path g x y p" and "v ∈ set p" and "¬ Blocked g p (B - {v})"
      using vB unfolding JustifiedBlock_def by blast
    then show "∃p. Path g x y p ∧ ¬ Blocked g p (B - {v})" by blast
  qed

  ― ‹Assemble final result›
  show ?thesis
    unfolding Weakly_minimal_def
    using all_blocked justified by blast
qed


end