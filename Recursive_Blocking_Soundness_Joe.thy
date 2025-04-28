theory Recursive_Blocking_Soundness_Joe
  imports Main
begin


(* Types for vertices and paths *)
typedecl node
type_synonym path = "node list"    ― ‹treat a path as a list of vertices›


(* Predicates *)
consts
  Coll :: "node ⇒ path ⇒ bool"                     (* x is a collider on path p *)
  NonC :: "node ⇒ path ⇒ bool"                     (* x is a non-collider on path p *)
  Endpoint :: "node ⇒ path ⇒ bool"                 (* x is an endpoint of path p *)
  (*OnPath :: "node ⇒ path ⇒ bool" *)                  (* x lies on path p *)
  AfterOnPath :: "node ⇒ node ⇒ path ⇒ bool"       (* x appears after y on path p *)
  Halts :: "node set ⇒ bool"                       (* recursive blocking halts *)
  ValidBlock :: "node set ⇒ bool"
  Growsto :: "node set ⇒ node set ⇒ bool"
  StrictSubset :: "node set ⇒ node set ⇒ bool"
  Initial :: "node set"
  Adj :: "node ⇒ node ⇒ bool"
  desc :: "node ⇒ node ⇒ bool"   ― ‹reflexive descendant›

(* Assumed sets *)
consts
  V :: "node set"                      (* Universe of nodes *)

text ‹A *walk* is a (non-empty) list of nodes in which every pair of
      consecutive nodes is adjacent.›
fun walk :: "node list ⇒ bool" where
  "walk []         ⟷ False" |
  "walk [_]        ⟷ True"  |
  "walk (x # y # ws) ⟷ Adj x y ∧ walk (y # ws)"

(* Definitions *)
definition HasNC_def: "HasNC p f ≡ ∃x. NonC x p ∧ x ∉ f"

definition NoAfterInB_def: "NoAfterInB v B p ≡ ∀d. AfterOnPath d v p ⟶ d ∉ B"

definition Blocked_after_def:
  "Blocked_after p B ≡ (∃x. NonC x p ∧ x ∈ B) ∨ (∀x. Coll x p ⟶ x ∉ B ∧ NoAfterInB x B p)"
                                                               
definition NoDescInB :: "node ⇒ node set ⇒ bool" where
  "NoDescInB c B ≡ ¬ (∃d. desc c d ∧ d ∈ B)"

definition Blocked_def :
  "Blocked p B ≡ (∃v. NonC v p ∧ v ∈ B)  ∨ (∀c. Coll c p ⟶ NoDescInB c B)"

definition Unblocked_after_def: "Unblocked p B ≡ ¬ Blocked_after p B"

definition SubsetV :: "node set ⇒ bool" where
  "SubsetV w ≡ w ⊆ V"

definition VSet :: "node set set" where
  "VSet ≡ {s. s ⊆ V}"

definition InVSet :: "node set ⇒ bool" where
  "InVSet x ≡ x ∈ VSet"

definition MSep :: "node ⇒ node ⇒ node set ⇒ bool" where
  "MSep x y B ≡ ¬ Adj x y ∧ (∀p. Blocked_after p B)"

definition Path :: "node ⇒ node ⇒ path ⇒ bool" where
  "Path x y p ⟷ hd p = x ∧ last p = y ∧ walk p"

definition OnPath :: "node ⇒ path ⇒ bool"  where
  "OnPath d p ≡ d ∈ set p"


axiomatization
  f   :: "node set"                   ― ‹the “not-follow” set›
and b1  :: "node set"                 ― ‹next blocking set›
where
  ax5:  "⋀p. Unblocked p B ⟹ HasNC p f ⟹ ∃x. NonC x p ∧ x ∈ b1" and
  ax6:  "⋀x p. NonC x p ⟹ x ∈ b1 ⟹ ¬ Halts B" and
  ax7:  "⋀x. x ∈ f ⟹ x ∉ B" and
  ax8:  "⋀p. (∃v. Coll v p ∧ v ∈ B) ⟹ ∃w. NonC w p ∧ w ∈ B" and
  ax9:  "⋀x p. Endpoint x p ⟹ x ∉ B" and
  ax10: "⋀x p. OnPath x p ⟹ Coll x p ∨ NonC x p ∨ Endpoint x p" and
  ax10a:"⋀d v p. AfterOnPath d v p ⟹ OnPath d p"

(* Only need one of the following two. The second is weaker. *)
(*axiomatization
  where desc_after:
    "⟦ desc c d; OnPath d p; Coll c p ⟧ ⟹ AfterOnPath d c p"*)

axiomatization
  where desc_after_in_B:
    "⟦ desc c d; d ∈ B; Path x y p; OnPath d p ⟧ ⟹ AfterOnPath d c p"

(*  Invariant: the algorithm can add a vertex v to B
    only at the moment it is *standing on v* while tracing
    an open walk from x to y. *)
axiomatization where
  AddedFromWalk: "⟦v ∈ B; Halts B⟧ ⟹ (∃p. Path x y p ∧ OnPath v p)"


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
  hence up1: "Unblocked p1 B" unfolding Unblocked_after_def by simp

  have "HasNC p1 f ∨ ¬ HasNC p1 f" by blast
  then show False
  proof
    assume hnc: "HasNC p1 f"
    from up1 hnc have "∃x. NonC x p1 ∧ x ∈ b1" using ax5 by blast
    then obtain a where "NonC a p1 ∧ a ∈ b1" by blast
    hence "¬ Halts B" using ax6 by blast
    thus False using h1 by contradiction
  next
    assume nhnc: "¬ HasNC p1 f"
    hence all_noncs_in_f: "∀x. NonC x p1 ⟶ x ∈ f"
      unfolding HasNC_def by blast
    hence nonc_part: "∀x. NonC x p1 ⟶ x ∉ B"
      using ax7 by blast

    {
      assume "∃v. Coll v p1 ∧ v ∈ B"
      then obtain w where "NonC w p1 ∧ w ∈ B" using ax8 by blast
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
        from ax10a[OF after] have on_path: "OnPath d p1" .
        have path_case: "Coll d p1 ∨ NonC d p1 ∨ Endpoint d p1"
          using ax10 on_path by blast

        show "d ∉ B"
        proof (rule disjE3[OF path_case])
          assume "Coll d p1"
          thus ?thesis using coll_part by blast
        next
          assume "NonC d p1"
          thus ?thesis using nonc_part by blast
        next
          assume "Endpoint d p1"
          thus ?thesis using ax9 by blast
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
     (∀p. Path x y p ⟶ length p ≥ 2 ⟶ Blocked_after p B)" 

lemma blocked_imp_blocked_after:
  assumes Path_p : "Path x y p"
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
  using BA col aft
  unfolding Blocked_after_def NoAfterInB_def
  sorry
(*─────────────────────────────────────────────────────────────────────────*)

(*  A very small “bridge’’: if d is a (strict) descendant of c
    and both lie on the same path p, then d occurs *after* c on p. *)
lemma Desc_Coll_imp_After:
  assumes "Coll c p"
      and "desc c d"
      and "OnPath d p"
  shows   "AfterOnPath d c p"
  using assms
  unfolding AfterOnPath_def desc_def OnPath_def
  sorry        (* adjust the unfoldings if your names differ *)
(*─────────────────────────────────────────────────────────────────────────*)
lemma exists_collider_after_descendant:
  assumes "Path x y p"  "OnPath d p"  "desc c d"
  shows   "∃c. Coll c p ∧ AfterOnPath d c p"
  sorry

lemma blocked_after_imp_blocked:
  assumes HB   : "Halts B"
      and Pxy  : "Path x y p"
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
        assume "∃d. desc c d ∧ d ∈ B"
        then obtain d where Ddesc: "desc c d" and DinB: "d ∈ B" by blast

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

          ― ‹AddedFromWalk gives *some* x–y path p₁ that contains d›
          obtain p1 where P1: "Path x y p1" and On1: "OnPath d p1"
            using AddedFromWalk DinB HB by blast

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


theorem blocked_equiv_len_ge:
  assumes HB     : "Halts B"
      and Path_p : "Path x y p"
      and len2   : "length p ≥ 2"
      and FPInv  : "FixPointInv x y B"
  shows "Blocked_after p B ⟷ Blocked p B"
  using blocked_after_imp_blocked[OF HB Path_p len2]
        blocked_imp_blocked_after[OF Path_p len2 FPInv]
  by blast


end
