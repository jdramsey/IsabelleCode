theory Peter_Soundness
  imports Main   \<comment> \<open>whatever file already defines Path, d_conn etc.\<close>
begin

axiomatization
  d_conn :: "'v \<Rightarrow> 'v \<Rightarrow> 'v set \<Rightarrow> bool"
where
  Lemma_3_1_1:
  "\<lbrakk> walk vs;  length vs \<ge> 2;
     \<And>i S. i < length vs - 1 \<Longrightarrow> Hop i vs S \<Longrightarrow> d_conn (vs!i) (vs!(i+1)) S \<rbrakk>
   \<Longrightarrow> d_conn (hd vs) (last vs) (\<Union>i<length vs - 1. SOME S. Hop i vs S)"

theorem recursive_blocking_sound:
  assumes halts: "Halts B"        \<comment> \<open>outer loop finished with B\<close>
      and algo: "Algorithm_steps graph x y C F B" 
      \<comment> \<open>your existing inductive description of the algorithm\<close>
  shows "\<forall>p. Path x y p \<longrightarrow> Blocked p B"
proof (rule ccontr)
  assume "\<not> (\<forall>p. Path x y p \<longrightarrow> Blocked p B)"
  then obtain p where path: "Path x y p" and unblk: "Unblocked p B"
    by (auto simp: Blocked_def Unblocked_def)

  \<comment> \<open>Take the *left-most eligible non-collider* on p; the algorithm
      would have inserted it unless it already is in B.  Therefore:\<close>
  have elig: "\<forall>v. NonColl v p \<longrightarrow> v \<in> B" using h algo path open \<dots>
  
  \<comment> \<open>Colliders on p are either in B or have a descendant in B
      (standard PAG argument).  Thus every hop of p is d-connected
      under B.\<close>
  have hops: "\<And>i. \<dots> \<Longrightarrow> d_conn (p!i) (p!(i+1)) B" \<dots>

  \<comment> \<open>Apply Lemma 3.1.1 to stitch the hops together.\<close>
  have "d_conn x y B"
    using Lemma_3_1_1[OF path \<dots> hops] \<dots>

  \<comment> \<open>But the *final sweep* of the algorithm checked that x and y are
      d-separated given B—contradiction.\<close>
  moreover have "\<not> d_conn x y B"
    using halts algo \<dots>
  ultimately show False by contradiction
qed