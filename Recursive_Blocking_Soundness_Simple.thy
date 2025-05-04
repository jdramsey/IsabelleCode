theory Recursive_Blocking_Soundness_Simple
  imports Main Graph_Theory_Simple HOL.Wellfounded
begin

consts Initial_B :: "node ⇒ node ⇒ 'c ⇒ 'f ⇒ graph ⇒ node set"

(* ------------------------------------------------------------------------- *)
subsection ‹Path-blocking definitions (unchanged)›
(* ------------------------------------------------------------------------- *)

definition HasNC :: "path ⇒ node set ⇒ bool" where
  "HasNC p B ≡ ∃x. NonC x p ∧ x ∉ B"

definition NoAfterInB :: "node ⇒ node set ⇒ path ⇒ bool" where
  "NoAfterInB v B p ≡ ∀d. AfterOnPath d v p ⟶ d ∉ B"

definition DirectedPath :: "node ⇒ node ⇒ node list ⇒ graph ⇒ bool" where
  "DirectedPath x y p G ≡
      p ≠ [] ∧ hd p = x ∧ last p = y ∧
      (∀i < length p - 1. Adj (p ! i) (p ! (i + 1)) G)"

definition Desc :: "node ⇒ node ⇒ graph ⇒ bool" where
  "Desc x y G ≡ ∃p. DirectedPath x y p G"

definition NoDescInB :: "node ⇒ node set ⇒ graph ⇒ bool" where
  "NoDescInB c B G ≡ ¬ (∃d. Desc c d G ∧ d ∈ B)"

definition ABlocked :: "path ⇒ node set ⇒ graph ⇒ bool" where
  "ABlocked p B G ≡ (∃v. NonC v p ∧ v ∈ B) ∨ (∀c. Coll c p ⟶ NoDescInB c B G)"

definition Unblocked :: "path ⇒ node set ⇒ graph ⇒ bool" where
  "Unblocked p B G ≡ ¬ ABlocked p B G"

definition MSep :: "node ⇒ node ⇒ node set ⇒ graph ⇒ bool" where
  "MSep x y B G ≡ ¬ Adj x y G ∧ (∀p. Path x y p G ⟶ ABlocked p B G)"

definition Path :: "node ⇒ node ⇒ path ⇒ graph ⇒ bool" where
  "Path x y p G ⟷ hd p = x ∧ last p = y ∧ walk p G"

definition walk_p :: "node list ⇒ graph ⇒ bool" where
  "walk_p p G ≡ walk p G"

definition ValidBlock :: "node set ⇒ graph ⇒ bool" where
  "ValidBlock B G ≡ ∀p c. Coll c p ⟶ NoDescInB c B G"

definition eligible_noncollider
  :: "node ⇒ node ⇒ node ⇒ node set ⇒ path ⇒ graph ⇒ bool"
     ("Eligible'_noncollider _ _ _ _ _ _" [100,100,100,100,100,100] 100)
  where
  "eligible_noncollider x y v B p G ≡
        Unblocked p B G
      ∧ Path x y p G
      ∧ NonC v p
      ∧ v ∉ B
      ∧ (∀w. NonC w p ∧ w ∉ B ⟶ AfterOnPath w v p)"

definition NextB :: "node set ⇒ node ⇒ node set"  where
  "NextB B0 v ≡ B0 ∪ {v}"

definition Halts :: "node set ⇒ node ⇒ node ⇒ graph ⇒ bool" where
  "Halts B x y G ≡ ¬ (∃p v. Path x y p G ∧ NonC v p ∧ v ∉ B ∧ ¬ ABlocked p B G)"

definition Weakly_minimal :: "node ⇒ node ⇒ node set ⇒ graph ⇒ bool" where
  "Weakly_minimal x y B G ≡
     (∀p. Path x y p G ⟶ ABlocked p B G)        
   ∧ (∀v ∈ B. ∃p. Path x y p G ∧ ¬ ABlocked p (B - {v}) G)"

(* ------------------------------------------------------------------------- *)
subsection ‹Three-way disjunction eliminator (helper lemma)›
(* ------------------------------------------------------------------------- *)

inductive RB_step
  :: "node ⇒ node ⇒ 'c ⇒ 'f ⇒ node set ⇒ node set ⇒ graph ⇒ bool"
where
  add_noncollider:
    "eligible_noncollider x y v B0 p G ⟹
     RB_step x y C F B0 (NextB B0 v) G"

inductive Algorithm_steps
    :: "node ⇒ node ⇒ 'c ⇒ 'f ⇒ node set ⇒ graph ⇒ bool"
where
  base:
    "Initial_B x y C F G = B ⟹
     Algorithm_steps x y C F B G"
| step:
    "RB_step x y C F B0 B1 G ⟹
     Algorithm_steps x y C F B1 G ⟹
     Algorithm_steps x y C F B0 G"

lemma disjE3:
  assumes "A ∨ B ∨ C"
    and AB: "A ⟹ R" and BB: "B ⟹ R" and CB: "C ⟹ R"
  shows R
  using assms by blast

axiomatization where
  InitialBlock_is_valid:
    "∀x y C F G. ValidBlock (Initial_B x y C F G) G"

(* New argument *)

axiomatization where
  interior_nodes_are_Coll_or_NonC:
    "OnPath v p ⟹ v ≠ hd p ⟹ v ≠ last p ⟹ (Coll v p ∨ NonC v p)"

lemma not_Coll_imp_NonC:
  assumes "OnPath v p"
      and "v ≠ hd p" and "v ≠ last p"
      and "¬ Coll v p"
  shows "NonC v p"
  using assms interior_nodes_are_Coll_or_NonC by blast

lemma unblocked_implies_collider_path:
  assumes halts: "Halts B x y G"
      and steps: "Algorithm_steps x y C F B G"
      and path: "Path x y p G"
      and not_blocked: "¬ ABlocked p B G"
  shows "∀v. OnPath v p ⟶ (v = hd p ∨ v = last p ∨ Coll v p)"
proof
fix v
show "OnPath v p ⟶ (v = hd p ∨ v = last p ∨ Coll v p)"
  proof
    assume on: "OnPath v p"
    show "v = hd p ∨ v = last p ∨ Coll v p"
    proof (cases "v = hd p ∨ v = last p")
      case True
      then show ?thesis by blast
    next
      case False
      then have interior: "v ≠ hd p" "v ≠ last p" by auto
  
      from interior_nodes_are_Coll_or_NonC[OF on interior(1) interior(2)]
      have cases: "Coll v p ∨ NonC v p" .
  
      then show ?thesis
      proof
        assume "Coll v p"
        then show ?thesis by simp
      next
        assume nc: "NonC v p"
        show ?thesis
        proof (cases "v ∈ B")
          case True
          then have "ABlocked p B G"
            unfolding ABlocked_def using nc by blast
          with not_blocked show ?thesis by contradiction
        next
          case False
          then have "∃p' v'. Path x y p' G ∧ NonC v' p' ∧ v' ∉ B ∧ ¬ ABlocked p' B G"
            using path nc not_blocked by blast
          then have "¬ Halts B x y G"
            unfolding Halts_def by blast
          with halts show ?thesis by contradiction
        qed
      qed
    qed
  qed
qed


(* ------------------------------------------------------------------------- *)
subsection ‹Soundness Theorem›
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
subsection ‹Justification and Regress›
(* ------------------------------------------------------------------------- *)

definition JustifiedInB :: "node ⇒ node set ⇒ node ⇒ node ⇒ graph ⇒ bool" where
  "JustifiedInB v B x y G ≡
     ∃p. Path x y p G ∧ NonC v p ∧ v ∈ set p ∧ v ∈ B ∧ ¬ ABlocked p (B - {v}) G"

inductive JustificationChain :: "(nat ⇒ node) ⇒ node set ⇒ node ⇒ node ⇒ graph ⇒ bool" where
  base:
    "JustifiedInB (f 0) B x y G ⟹ JustificationChain f B x y G"
| step:
    "JustificationChain f B x y G ⟹
     JustifiedInB (f (Suc n)) B x y G ⟹
     Desc (f n) (f (Suc n)) G ⟹
     JustificationChain f B x y G"

lemma regress_chain_finite:
  assumes fin: "finite (V G)"
      and just: "∀v ∈ B. JustifiedInB v B x y G"
  shows "¬ (∃f :: nat ⇒ node. inj_on f UNIV ∧ (∀i. f i ∈ B))"
proof
  assume "∃f :: nat ⇒ node. inj_on f UNIV ∧ (∀i. f i ∈ B)"
  then obtain f :: "nat ⇒ node" where inj: "inj_on f UNIV" and inB: "∀i. f i ∈ B"
    by blast

  have "B ⊆ V G"
  proof
    fix v assume "v ∈ B"
    from just[rule_format, OF ‹v ∈ B›]
    obtain p where P: "Path x y p G" and NC: "NonC v p" and In: "v ∈ set p" and NB: "¬ ABlocked p (B - {v}) G"
      unfolding JustifiedInB_def by blast
    hence "v ∈ set p" by blast
    then show "v ∈ V G"
      using ‹Path x y p G› unfolding Path_def
      by (metis in_set_conv_nth)
  qed

  from ‹B ⊆ V G› fin have "finite B"
    by (rule finite_subset)

  have inj_f: "inj f"
    using inj unfolding inj_on_def by simp
  
  have "range f ⊆ B"
    using inB by auto

  have "infinite (range f)"
    using inj_f infinite_UNIV_nat by (metis inj_on_def inj_on_subset range_subsetD)
  
  from ‹finite B› ‹range f ⊆ B› ‹infinite (range f)›
  show False
    using finite_subset by blast

qed

lemma all_nodes_in_B_are_justified:
  assumes steps: "Algorithm_steps x y C F B G"
  shows "∀v ∈ B. JustifiedInB v B x y G"
  using steps
  sorry
(*proof (induction x y C F B G rule: Algorithm_steps.induct)
  case (base x y C F B G)
  ― ‹Initial_B gives us B directly. It may be empty ⇒ vacuously true›
  then show "∀v ∈ B. JustifiedInB v B x y G"
    unfolding JustifiedInB_def by blast
next
  case (step x y C F B0 B1 G)
  ― ‹We have RB_step from B0 to B1, and IH for B1›

  have IH: "∀v ∈ B1. JustifiedInB v B1 x y G"
    using step.IH by blast

  ― ‹From RB_step, v was added to B0 to get B1›
  obtain v p where
    eligible: "eligible_noncollider x y v B0 p G"
    and B1_eq: "B1 = B0 ∪ {v}"
    using step.hyps(1) unfolding RB_step.simps by blast

  show "∀v' ∈ B0. JustifiedInB v' B0 x y G"
  proof
    fix v'
    assume "v' ∈ B0"
    then have "v' ∈ B1" using B1_eq by blast
    from IH[rule_format, OF this]
    ― ‹v' justified in B1 ⇒ also justified in B0›
    ― ‹JustifiedInB allows weakening of B if v' ≠ v›
    show "JustifiedInB v' B0 x y G"
      unfolding JustifiedInB_def
      using ‹v' ∈ B0› by blast
  qed

  ― ‹Also justify the newly added node v›
  have "JustifiedInB v B0 x y G"
  proof -
    from eligible have path: "Path x y p G"
      and nonc: "NonC v p"
      and notinB: "v ∉ B0"
      and unblocked: "¬ ABlocked p B0 G"
      and first: "∀w. NonC w p ∧ w ∉ B0 ⟶ AfterOnPath w v p"
      unfolding eligible_noncollider_def by blast+

    show ?thesis
      unfolding JustifiedInB_def
      by (intro exI[of _ p]) (auto simp: path nonc unblocked)
  qed

  ― ‹Put everything together: all of B0 ∪ {v} is justified›
  with B1_eq show "∀v ∈ B0. JustifiedInB v B0 x y G"
    by blast
qed*)

lemma regress_chain_exists_if_unblocked:
  assumes path: "Path x y p G"
      and not_blocked: "¬ ABlocked p B G"
      and steps: "Algorithm_steps x y C F B G"
    shows "∃f :: nat ⇒ node. inj_on f UNIV ∧ (∀i. f i ∈ B)"
  sorry

theorem regress_argument_soundness:
  assumes fin: "finite (V G)"
      and steps: "Algorithm_steps x y C F B G"
      and halts: "Halts B x y G"
  shows "∀p. Path x y p G ⟶ ABlocked p B G"
proof
  fix p
  show "Path x y p G ⟶ ABlocked p B G"
  proof
    assume path: "Path x y p G"
    show "ABlocked p B G"
    proof (rule ccontr)
      assume not_blocked: "¬ ABlocked p B G"

      from halts steps path not_blocked
      have collider_path: "∀v. OnPath v p ⟶ (v = hd p ∨ v = last p ∨ Coll v p)"
        by (rule unblocked_implies_collider_path)

      ― ‹Assume that all nodes added to B were justified›
      have all_justified: "∀v ∈ B. JustifiedInB v B x y G"
        using steps by (rule all_nodes_in_B_are_justified)

      then have "¬ (∃f :: nat ⇒ node. inj_on f UNIV ∧ (∀i. f i ∈ B))"
        using fin regress_chain_finite by blast

      from path not_blocked steps
      have chain: "∃f :: nat ⇒ node. inj_on f UNIV ∧ (∀i. f i ∈ B)"
        by (rule regress_chain_exists_if_unblocked)

      have no_chain: "¬ (∃f :: nat ⇒ node. inj_on f UNIV ∧ (∀i. f i ∈ B))"
        using fin all_justified by (rule regress_chain_finite)

       from chain no_chain show False by contradiction
    qed
  qed
qed

lemma blocking_set_is_weakly_minimal:
  assumes steps: "Algorithm_steps x y C F B G"
      and halts: "Halts B x y G"
      and fin: "finite (V G)"
  shows "Weakly_minimal x y B G"
proof -
  have all_blocked: "∀p. Path x y p G ⟶ ABlocked p B G"
    using fin steps halts by (rule regress_argument_soundness)

  have justified: "∀v ∈ B. ∃p. Path x y p G ∧ ¬ ABlocked p (B - {v}) G"
  proof
    fix v assume "v ∈ B"
    from all_nodes_in_B_are_justified[OF steps, rule_format, OF this]
    obtain p where "Path x y p G" and "¬ ABlocked p (B - {v}) G"
      unfolding JustifiedInB_def by blast
    then show "∃p. Path x y p G ∧ ¬ ABlocked p (B - {v}) G" by blast
  qed

  show ?thesis
    unfolding Weakly_minimal_def using all_blocked justified by blast
qed

end
