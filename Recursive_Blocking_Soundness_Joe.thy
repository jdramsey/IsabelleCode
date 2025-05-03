theory Recursive_Blocking_Soundness_Joe
  imports Main HOL.List
begin                 


(* Types for vertices and paths *)
typedecl node
type_synonym path = "node list"    ― ‹treat a path as a list of nodes›


(* Predicates *)
consts
  NonC :: "node ⇒ path ⇒ bool"                     (* x is a non-collider on path p *)
  Endpoint :: "node ⇒ path ⇒ bool"                 (* x is an endpoint of path p *)
  Halts :: "node set ⇒ bool"                       (* recursive blocking halts *)
  ValidBlock :: "node set ⇒ bool"
  Growsto :: "node set ⇒ node set ⇒ bool"
  StrictSubset :: "node set ⇒ node set ⇒ bool"
  Initial :: "node set"
  Adj :: "node ⇒ node ⇒ bool"

(* Assumed sets *)
consts
  V :: "node set"                      (* Universe of nodes *)

text ‹A *walk* is a (non-empty) list of nodes in which every pair of
      consecutive nodes is adjacent.›
fun walk :: "node list ⇒ bool" where
  "walk []         ⟷ False" |
  "walk [_]        ⟷ True"  |
  "walk (x # y # ws) ⟷ Adj x y ∧ walk (y # ws)"

fun myindex :: "'a list ⇒ 'a ⇒ nat" where
  "myindex [] x = 0" |  "myindex (y # ys) x = (if x = y then 0 else 1 + myindex ys x)"

definition directed_edge :: "node ⇒ node ⇒ bool" where
  "directed_edge x y ≡ Adj x y"

(* Definitions *)  
definition HasNC: "HasNC p f ≡ ∃x. NonC x p ∧ x ∉ f"

definition DirectedPath :: "node ⇒ node ⇒ path ⇒ bool" where
  "DirectedPath x y p ≡
     p ≠ [] ∧ hd p = x ∧ last p = y ∧ (∀i < length p - 1. Adj (p ! i) (p ! (i + 1)))"
                            
definition Pathxy :: "node ⇒ node ⇒ path ⇒ bool" where
  "Pathxy x y p ≡ hd p = x ∧ last p = y ∧ walk p"

definition OnPath :: "node ⇒ path ⇒ bool"  where
  "OnPath d p ≡ d ∈ set p"

definition AfterOnPath :: "node ⇒ node ⇒ path ⇒ bool" where
  "AfterOnPath u v p ≡ ∃i j. i < j ∧ j < length p ∧ p ! i = v ∧ p ! j = u"

definition BeforeOnPath :: "node ⇒ node ⇒ path ⇒ bool" where
  "BeforeOnPath u v p ≡ ∃i j. i < j ∧ j < length p ∧ p ! i = u ∧ p ! j = v"

definition NoAfterInB where
  "NoAfterInB v B p ≡ ∀d. AfterOnPath d v p ⟶ d ∉ B"

definition Coll :: "node ⇒ node list ⇒ bool" where
  "Coll c p ≡ c ∈ set p"

(*definition Desc :: "node ⇒ node ⇒ bool" where
  "Desc x y ≡ (∃p. DirectedPath x y p)"*)

(*definition Desc :: "node ⇒ node ⇒ bool" where
  "Desc c d ≡ (∃p. DirectedPath c d p ∧ distinct p ∧ c ≠ d)"*)

(*definition Desc :: "node ⇒ node ⇒ bool" where
  "Desc x y ≡ (∃p. DirectedPath x y p) ∧ ¬ (∃q. DirectedPath y x q)"*)

definition Desc :: "node ⇒ node ⇒ bool" where
  "Desc x y ≡ (∃p. DirectedPath x y p) ∧ (x = y ∨ ¬ (∃q. DirectedPath y x q))"
                                                               
definition NoDescInB :: "node ⇒ node set ⇒ bool" where
  "NoDescInB c B ≡ ¬ (∃d. Desc c d ∧ d ∈ B)"

definition Blocked where
  "Blocked p B ≡ (∃v. NonC v p ∧ v ∈ B) ∨ (∀c. Coll c p ⟶ NoDescInB c B)"

definition Blocked_after where
  "Blocked_after p B ≡ (∃x. NonC x p ∧ x ∈ B) ∨ (∀x. Coll x p ⟶ x ∉ B ∧ NoAfterInB x B p)"

definition Unblocked: "Unblocked p B ≡ ¬ Blocked_after p B"

definition Unblocked_after: "Unblocked_after p B ≡ ¬ Blocked_after p B"

definition SubsetV :: "node set ⇒ bool" where
  "SubsetV w ≡ w ⊆ V"

definition VSet :: "node set set" where
  "VSet ≡ {s. s ⊆ V}"

definition InVSet :: "node set ⇒ bool" where
  "InVSet x ≡ x ∈ VSet"

definition MSep :: "node ⇒ node ⇒ node set ⇒ bool" where
  "MSep x y B ≡ ¬ Adj x y ∧ (∀p. Blocked_after p B)"


axiomatization
  f   :: "node set"                   ― ‹the “not-follow” set›
and b1  :: "node set"                 ― ‹next blocking set›
where
  ax1:  "⋀p. Unblocked p B ⟹ HasNC p f ⟹ ∃x. NonC x p ∧ x ∈ b1" and
  ax2:  "⋀x p. NonC x p ⟹ x ∈ b1 ⟹ ¬ Halts B" and
  ax3:  "⋀x. x ∈ f ⟹ x ∉ B" and
  ax4:  "⋀p. (∃v. Coll v p ∧ v ∈ B) ⟹ ∃w. NonC w p ∧ w ∈ B" and
  ax5:  "⋀x p. Endpoint x p ⟹ x ∉ B" and
  ax6:  "⋀x p. OnPath x p ⟹ Coll x p ∨ NonC x p ∨ Endpoint x p" and
  ax7:  "⋀d v p. AfterOnPath d v p ⟹ OnPath d p"

axiomatization
  where desc_after_in_B:
    "⟦ Desc c d; d ∈ B; Pathxy x y p; OnPath d p ⟧ ⟹ AfterOnPath d c p"

(*  Invariant: the algorithm can add a vertex v to B
    only at the moment it is *standing on v* while tracing
    an open walk from x to y. *)
axiomatization where
  added_from_walk: "⟦v ∈ B; Halts B⟧ ⟹ (∃p. Pathxy x y p ∧ OnPath v p)"


(* 3-way disjunction eliminator *)
lemma disjE3:
  assumes "A ∨ B ∨ C"
    and "A ⟹ R"
    and "B ⟹ R"
    and "C ⟹ R"
  shows R
  using assms by blast

(* Theorem: Soundness of Recursive Blocking *)
theorem fixpoint:
  assumes h1: "Halts B"
  shows "∀p. Blocked_after p B"
proof (rule ccontr)
  assume "¬ (∀p. Blocked_after p B)"
  then obtain p1 where p1_unblocked: "¬ Blocked_after p1 B" by blast
  hence unbl_p1: "Unblocked p1 B" unfolding Unblocked by simp

  have "HasNC p1 f ∨ ¬ HasNC p1 f" by blast
  then show False
  proof
    assume hnc: "HasNC p1 f"
    from unbl_p1 hnc have "∃x. NonC x p1 ∧ x ∈ b1" using ax1 by blast
    then obtain a where "NonC a p1 ∧ a ∈ b1" by blast
    hence "¬ Halts B" using ax2 by blast
    thus False using h1 by contradiction
  next
    assume not_has_nc: "¬ HasNC p1 f"
    hence all_noncs_in_f: "∀x. NonC x p1 ⟶ x ∈ f"
      unfolding HasNC by blast
    hence nonc_part: "∀x. NonC x p1 ⟶ x ∉ B"
      using ax3 by blast

    {
      assume "∃v. Coll v p1 ∧ v ∈ B"
      then obtain w where "NonC w p1 ∧ w ∈ B" using ax4 by blast
      hence "NonC w p1" and "w ∈ B" by blast+
      hence "w ∉ B" using nonc_part by blast 
      hence False using ‹w ∈ B› by contradiction
    }

    hence no_coll_in_b: "¬ (∃v. Coll v p1 ∧ v ∈ B)" by blast
    hence coll_part: "∀v. Coll v p1 ⟶ v ∉ B" by blast

    have coll_no_after: "∀v. Coll v p1 ⟶ NoAfterInB v B p1"
    proof (intro allI impI)
      fix c1
      assume coll_c1: "Coll c1 p1"
      show "NoAfterInB c1 B p1"
      proof (unfold NoAfterInB_def, intro allI impI)
        fix d
        assume after: "AfterOnPath d c1 p1"
        from ax7[OF after] have on_path: "OnPath d p1" .
        have path_case: "Coll d p1 ∨ NonC d p1 ∨ Endpoint d p1"
          using ax6 on_path by blast

        show "d ∉ B"
        proof (rule disjE3[OF path_case])
          assume "Coll d p1"
          thus ?thesis using coll_part by blast
        next
          assume "NonC d p1"
          thus ?thesis using nonc_part by blast
        next
          assume "Endpoint d p1"
          thus ?thesis using ax5 by blast
        qed
      qed
    qed

    have "Blocked_after p1 B"
      unfolding Blocked_after_def
      using nonc_part coll_part coll_no_after
      by blast
    thus False using p1_unblocked by contradiction
  qed
qed

(* If we add one variable at a time to the blocking set, never removing
any,  and there is only a finite set of variables, the procedure must halt. *)
lemma termination_lemma:
  fixes   V  :: "'a set"             ― ‹finite universe of vertices›
    and   B  :: "'a set"             ― ‹initial blocking set (e.g. C)›
    and   Halts :: "'a set ⇒ bool"    ― ‹predicate defined elsewhere›
  assumes finV: "finite V"
      and init : "B ⊆ V"
      and grow : "⋀B. B ⊆ V ⟹ ¬ Halts B ⟹ (∃B'. B ⊂ B' ∧ B' ⊆ V)"
      ― ‹“one outer sweep strictly enlarges B unless Halts B”›
  shows "∃B. Halts B"
  sorry

theorem completeness:
  assumes termination_lemma: "∃B. Halts B"
    and fixpoint: "⋀B. Halts B ⟹ ∀p. Blocked_after p B"
    and growth_invariant: "⋀B. Halts B ⟹ Initial ⊆ B"
  shows "∃B. Halts B ∧ Initial ⊆ B ∧ (∀p. Blocked_after p B)"
proof -
  obtain B where hb: "Halts B" using termination_lemma by blast
  have blocked: "∀p. Blocked_after p B" using fixpoint hb by blast
  have subset: "Initial ⊆ B" using growth_invariant hb by blast
  show ?thesis
    using hb subset blocked by blast
qed

lemma corollary_msep:
  assumes "Halts B"
    and "¬ Adj x y"
    and fixpoint: "Halts B ⟶ (∀p. Blocked_after p B)"
  shows "MSep x y B"
proof -
  from assms(1) fixpoint have "∀p. Blocked_after p B" by blast
  with assms(2) show ?thesis
    unfolding MSep_def by blast
qed

lemma msep_implies_not_adj:
  assumes "MSep x y B"
  shows "¬ Adj x y"
  using assms unfolding MSep_def by blast

lemma corollary_msep_transfer:
  assumes "Halts B_halt"
    and "∃B_star. MSep x y B_star"
    and fixpoint: "Halts B_halt ⟶ (∀p. Blocked_after p B_halt)"
  shows "MSep x y B_halt"
proof -
  obtain B_star where "MSep x y B_star" using assms(2) by blast
  then have "¬ Adj x y" using msep_implies_not_adj by blast
  moreover have "∀p. Blocked_after p B_halt"
    using assms(1) assms(3) by blast
  ultimately show ?thesis
    unfolding MSep_def by blast
qed

(* A simple consequence/restating of the fixed point lemma. *)

definition FixPointInv ::
  "node ⇒ node ⇒ node set ⇒ bool"   (*  x     y      B  *)
where
  "FixPointInv x y B ≡
     (∀p. Pathxy x y p ⟶ length p ≥ 2 ⟶ Blocked_after p B)" 

lemma blocked_imp_blocked_after:
  assumes Path_p : "Pathxy x y p"
      and len2   : "length p ≥ 2"
      and FPInv  : "FixPointInv x y B"
      and Bl     : "Blocked p B"
  shows   "Blocked_after p B"
proof (cases "∃v. NonC v p ∧ v ∈ B")
  case True
  then show ?thesis
    unfolding Blocked_after_def by blast
next
  case False
  ― ‹no non-collider from p is in B, so use the fix-point invariant›
  show ?thesis
    using FPInv Path_p len2
    unfolding FixPointInv_def by blast
qed

(*─────────────────────────────────────────────────────────────────────────*)
lemma after_collider_not_in_B:
  assumes BA : "Blocked_after p B"
      and col: "Coll c p"
      and aft: "AfterOnPath d c p"
  shows   "d ∉ B"
proof -
  from BA have "(∃x. NonC x p ∧ x ∈ B) ∨ (∀x. Coll x p ⟶ x ∉ B ∧ NoAfterInB x B p)"
    unfolding Blocked_after_def by simp
  then show ?thesis
  proof
    assume "∃x. NonC x p ∧ x ∈ B"
    then show ?thesis sorry
  next
    assume H: "∀x. Coll x p ⟶ x ∉ B ∧ NoAfterInB x B p"
    from col have "Coll c p" by assumption
    then have "c ∉ B ∧ NoAfterInB c B p" using H by auto
    then have "NoAfterInB c B p" by simp
    then have "∀d'. AfterOnPath d' c p ⟶ d' ∉ B"
      unfolding NoAfterInB_def by simp
    thus ?thesis
      using aft by simp
  qed
qed

lemma Coll_min_length:
  assumes "Coll c p"
  shows "length p ≥ 3"
  sorry  ― ‹To be proved from the structure of your Coll predicate›

(*─────────────────────────────────────────────────────────────────────────*)

(*  A very small “bridge’’: if d is a (strict) descendant of c
    and both lie on the same path p, then d occurs *after* c on p. *)
lemma Desc_Coll_imp_After:
  assumes coll: "Coll c p"
      and desc: "Desc c d"
      and onpath: "OnPath d p"
      and neq: "d ≠ c"
  shows "AfterOnPath d c p"
proof (rule ccontr)
  assume not_after: "¬ AfterOnPath d c p"

  ― ‹Expand Desc: directed path from c to d›
  from desc obtain q where dir: "DirectedPath c d q"
    unfolding Desc_def by blast

  from dir have hd: "hd q = c" and last: "last q = d" and q_nonempty: "q ≠ []"
    unfolding DirectedPath_def by auto

  ― ‹From onpath and ¬AfterOnPath, deduce d appears before c›
  from onpath not_after have "BeforeOnPath d c p"
    unfolding AfterOnPath_def BeforeOnPath_def by blast

  ― ‹Now: if d appears before c on p, and there’s a DirectedPath c →+ d,
       then p contains a backward step from d to c, forming a cycle.›
  ― ‹So p must contain both a forward DirectedPath c →+ d and an implicit path d → ... → c›

  ― ‹That implies a DirectedPath from d to c exists, contradicting Desc›
  have "∃r. DirectedPath d c r"
    sorry ― ‹To be proven from BeforeOnPath d c p and adjacency of p›

  then show False
    using desc unfolding Desc_def using neq by blast
qed

(*─────────────────────────────────────────────────────────────────────────*)

lemma exists_collider_after_descendant:
  assumes Pxy  : "Pathxy x y p"
      and On   : "OnPath d p"
      and Desc : "Desc c0 d"
    shows "∃c. Coll c p ∧ AfterOnPath d c p"
proof -
  ― ‹Index of d in p›
  obtain k where k: "k < length p" "d = p ! k"
    using On unfolding OnPath_def in_set_conv_nth by blast

  ― ‹Define j = largest index < k such that edge (p!j)→… is directed
        toward d; such a j exists because Desc gives a forward chain
        into d.›
  define j where "j = (LEAST j. j < k ∧ directed_edge (p ! j) (p ! (j+1)))"

  have j_bounds: "j < k"
    unfolding j_def using k(1) by (rule LeastI_ex) (use Desc k in ‹blast›)

  ― ‹That j is a collider and lies before d›
  have Coll_j: "Coll (p ! j) p"
    by (simp add: Coll_first_before Pxy j_bounds j_def)   (* your lemma *)

  have After: "AfterOnPath d (p ! j) p"
    using j_bounds k unfolding AfterOnPath_def by auto

  show ?thesis
    by (intro exI[of _ "p ! j"]) (use Coll_j After in blast)
qed

lemma blocked_after_imp_blocked:
  assumes HB   : "Halts B"
      and Pxy  : "Pathxy x y p"
      and len2 : "length p ≥ 2"
      and BA   : "Blocked_after p B"
  shows "Blocked p B"
proof -
  ― ‹Rewrite the given “blocked-after’’ fact into the explicit disjunction›
  have Disj:
       "(∃v. NonC v p ∧ v ∈ B) ∨
        (∀c. Coll c p ⟶ c ∉ B ∧ (∀d. AfterOnPath d c p ⟶ d ∉ B))"
    using BA unfolding Blocked_after_def NoAfterInB_def by blast

  ― ‹Case split on which disjunct actually holds›
  from Disj show ?thesis
  proof
    ― ‹(1)  A non-collider on p is in B  ⇒  already “Blocked’’›
    assume "∃v. NonC v p ∧ v ∈ B"
    thus "Blocked p B"
      unfolding Blocked_def by blast

  next
    ― ‹(2)  No non-collider of p lies in B.  Show every collider
           has **no descendant** in B, hence p is “Blocked’’.›
    assume H: "∀c. Coll c p ⟶ c ∉ B ∧ (∀d. AfterOnPath d c p ⟶ d ∉ B)"

    have all_col_no_desc: "∀c. Coll c p ⟶ NoDescInB c B"
    proof (intro allI impI)
      fix c  assume C: "Coll c p"
      show "NoDescInB c B"
      proof (unfold NoDescInB_def, rule notI)
        assume "∃d. Desc c d ∧ d ∈ B"
        then obtain d where Ddesc: "Desc c d" and DinB: "d ∈ B" by blast

        ― ‹Split the trivial “d = c’’ vs “proper descendant’’ sub-case›
        consider (self) "d = c" | (proper) "d ≠ c" by blast
        then show False
        proof cases
          ― ‹(a)  d = c contradicts H›
          case self
          hence "c ∈ B" using DinB by simp
          moreover from H C have "c ∉ B" by blast
          ultimately show False by contradiction

        next
          ― ‹(b)  proper descendant›
          case proper

          ― ‹added_from_walk gives *some* x–y path p₁ that contains d›
          obtain p1 where P1: "Pathxy x y p1" and On1: "OnPath d p1"
            using added_from_walk DinB HB by blast

          ― ‹If that witness path happens to be the current p,
               the contradiction is immediate…›
          show False
          proof (cases "p1 = p")
            case True
            then have Onp: "OnPath d p" using On1 by simp

            have aft: "AfterOnPath d c p"
              using Desc_Coll_imp_After[OF C Ddesc Onp] .
            have "d ∉ B"
              by (rule after_collider_not_in_B[OF BA C aft])

            with DinB show False by contradiction
            next
              case False  ― ‹p1 ≠ p›
            
              ― ‹Every x–y path is blocked after the algorithm halts›
              have BA1: "Blocked_after p1 B"
                using fixpoint[OF HB] by blast     ― ‹your global fix-point lemma›
            
              ― ‹Find a collider on p1 that precedes d›
              obtain c1 where C1: "Coll c1 p1" and aft1: "AfterOnPath d c1 p1"
                using exists_collider_after_descendant[OF P1 On1 Ddesc] by blast
            
              ― ‹That collider closes p1, so d ∉ B›
              have NotInB: "d ∉ B"
                by (rule after_collider_not_in_B[OF BA1 C1 aft1])
            
              from DinB NotInB show False
                by blast
           qed
        qed
      qed
    qed

    ― ‹Universal statement is one of the clauses in Blocked_def›
    thus "Blocked p B"
      unfolding Blocked_def by blast
  qed
qed


theorem blocked_equiv:
  assumes HB     : "Halts B"
      and Path_p : "Pathxy x y p"
      and len2   : "length p ≥ 2"
      and FPInv  : "FixPointInv x y B"
  shows "Blocked_after p B ⟷ Blocked p B"
  using blocked_after_imp_blocked[OF HB Path_p len2]
        blocked_imp_blocked_after[OF Path_p len2 FPInv]
  by blast


end
