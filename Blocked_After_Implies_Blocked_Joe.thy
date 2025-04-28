theory Blocked_After_Implies_Blocked_Joe
  imports Main
begin

(* ------------- 1  Paths are lists of vertices ------------------------- *)

type_synonym 'p path = "'p list"

(* ------------- 2  Abstract graph-level notions and “after’’ ----------- *)

locale Graph_Stuff =
  fixes is_collider    :: "'p \<Rightarrow> bool"
    and is_noncollider :: "'p \<Rightarrow> bool"
    and after          :: "'p \<Rightarrow> 'p \<Rightarrow> 'p path \<Rightarrow> bool"
        \<comment> \<open>after c d p  \<equiv>  vertex d occurs strictly after c on walk p\<close>
    and desc           :: "'p \<Rightarrow> 'p \<Rightarrow> bool"       \<comment> \<open>reflexive descendant\<close>
    and Path           :: "'p \<Rightarrow> 'p \<Rightarrow> 'p path \<Rightarrow> bool"
        \<comment> \<open>your existing walk predicate: vertices x \<dots> y along p\<close>
  assumes desc_refl  : "desc v v"
    and desc_after_in_B   :
        "\<lbrakk> is_collider c; desc c d; d \<noteq> c; d \<in> B;
           Path x y p \<rbrakk>
         \<Longrightarrow> after c d p"
begin

(* ------------- 3  Auxiliary abbreviation ----------------------------- *)

abbreviation NoDescInB :: "'p \<Rightarrow> 'p set \<Rightarrow> bool"
  where  "NoDescInB c B \<equiv> \<not> (\<exists>d. desc c d \<and> d \<in> B)"

(* ------------- 4  Path-level predicates ------------------------------ *)

definition block_after :: "'p path \<Rightarrow> 'p set \<Rightarrow> bool" where
  "block_after p B \<longleftrightarrow>
       (\<exists>v. is_noncollider v \<and> v \<in> B)                 \<or>
       (\<forall>c. is_collider c \<longrightarrow> c \<notin> B \<and> (\<forall>d. after c d p \<longrightarrow> d \<notin> B))"

definition blocked :: "'p path \<Rightarrow> 'p set \<Rightarrow> bool" where
  "blocked p Z \<longleftrightarrow>
       (\<exists>v. is_noncollider v \<and> v \<in> Z)  \<or>
       (\<forall>c. is_collider c \<and> c \<in> set p \<longrightarrow> NoDescInB c Z)"

(* ------------- 5  Main lemma ----------------------------------------- *)

lemma blocked_after_imp_blocked:
  assumes Path_p  : "Path x y p"
      and MB : "block_after p B"
  shows "blocked p B"
proof -
  \<comment> \<open>Unfold the disjunction coming from block_after\<close>
  have Disj:
      "(\<exists>v. is_noncollider v \<and> v \<in> B) \<or>
       (\<forall>c. is_collider c \<longrightarrow> c \<notin> B \<and> (\<forall>d. after c d p \<longrightarrow> d \<notin> B))"
    using MB by (auto simp: Blocked_after_def)

  \<comment> \<open>Split the two cases\<close>
  then show ?thesis
  proof
    \<comment> \<open>1. Some non-collider lies in B\<close>
    assume "\<exists>v. is_noncollider v \<and> v \<in> B"
    then obtain v where "is_noncollider v" "v \<in> B" by blast
    thus ?thesis by (auto simp: blocked_def)

  next
    \<comment> \<open>2. Universal collider clause holds\<close>
    assume H: "\<forall>c. is_collider c \<longrightarrow> c \<notin> B \<and> (\<forall>d. after c d p \<longrightarrow> d \<notin> B)"

    have "\<forall>c. is_collider c \<longrightarrow> NoDescInB c B"
    proof (intro allI impI)
      fix c assume C: "is_collider c"
      show "NoDescInB c B"
      proof (rule ccontr)
        assume "\<not> NoDescInB c B"
        then obtain d where D: "desc c d" "d \<in> B" by blast
        consider (self) "d = c" | (proper) "d \<noteq> c" by blast
        then show False
        proof cases
          case self
          hence "c \<in> B" using D(2) by simp
          moreover from H C have "c \<notin> B" by auto
          ultimately show False by blast
        next
          case proper
          \<comment> \<open>d is a proper descendant: use the bridge lemma to get “after’’\<close>
          have after_cd: "after c d p"
            using desc_after_in_B[OF C D(1) proper D(2) Path_p] .
          have no_after: "\<forall>d. after c d p \<longrightarrow> d \<notin> B"
            using H C by auto
          have "d \<notin> B" using no_after after_cd by blast
          with D(2) show False by blast
        qed
      qed
    qed
    thus ?thesis by (auto simp: blocked_def)
  qed
qed

end  (*––– locale Graph_Stuff –––*)

end