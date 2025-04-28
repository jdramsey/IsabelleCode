theory Graph_Theory_Peter
  imports Main
begin

text \<open>Generic graph-theoretic definitions and d-separation lemmas used
      throughout the project.\<close>

(* ---------------------------------------------------------------- *)
section \<open>Primitive notions\<close>
(* ---------------------------------------------------------------- *)

typedecl node                    \<comment> \<open>vertex (node) type\<close>
type_synonym path = "node list"    \<comment> \<open>treat a path as a list of vertices\<close>

consts
  Adj      :: "node \<Rightarrow> node \<Rightarrow> bool"           \<comment> \<open>directed adjacency\<close>
  collider :: "node \<Rightarrow> node \<Rightarrow> node \<Rightarrow> bool"     \<comment> \<open>middle vertex is a collider\<close>
  noncoll  :: "node \<Rightarrow> node \<Rightarrow> node \<Rightarrow> bool"     \<comment> \<open>middle vertex is a non-collider\<close>

text \<open>A *walk* is a (non-empty) list of vertices in which every pair of
      consecutive vertices is adjacent.\<close>
fun walk :: "node list \<Rightarrow> bool" where
  "walk []         \<longleftrightarrow> False" |
  "walk [_]        \<longleftrightarrow> True"  |
  "walk (x # y # ws) \<longleftrightarrow> Adj x y \<and> walk (y # ws)"

(* ---------------------------------------------------------------- *)
section \<open>Activation along a walk\<close>
(* ---------------------------------------------------------------- *)

definition active :: "node list \<Rightarrow> node set \<Rightarrow> bool" where
  "active vs S \<longleftrightarrow>
     walk vs \<and>
     (let n = length vs in
        (\<forall>i. 0 < i \<and> i + 1 < n \<longrightarrow>
             ((noncoll (vs ! (i - 1)) (vs ! i) (vs ! (i + 1)) \<longrightarrow> vs ! i \<notin> S) \<and>
              (collider (vs ! (i - 1)) (vs ! i) (vs ! (i + 1)) \<longrightarrow> vs ! i \<in> S))))"

definition d_conn :: "node \<Rightarrow> node \<Rightarrow> node set \<Rightarrow> bool" where
  "d_conn x y S \<longleftrightarrow> (\<exists>P. hd P = x \<and> last P = y \<and> active P S)"

(* ---------------------------------------------------------------- *)
section \<open>Fundamental helper lemmas (placeholders for now)\<close>
(* ---------------------------------------------------------------- *)

lemma walk_concat_single:
  assumes "walk (xs @ [v])"
      and "walk (v # ys)"
  shows   "walk (xs @ (v # ys))"
  sorry

lemma active_append:
  assumes seg1: "active (xs @ [a]) S1"
      and seg2: "active (a # ys)  S2"
      and mid:  "(noncoll (last xs) a (hd ys) \<longrightarrow> a \<notin> S2) \<and>
                 (collider (last xs) a (hd ys) \<longrightarrow> a \<in> S1)"
  shows  "active (xs @ a # ys) (S1 \<union> S2)"
  sorry

lemma d_conn_bridge:
  assumes "d_conn x a T1" and "d_conn a y T2"
      and "(noncoll x a a \<and> a \<notin> T2) \<or> (collider x a a \<and> a \<in> T1)"
  shows  "d_conn x y (T1 \<union> T2)"
  sorry

(* ---------------------------------------------------------------- *)
section \<open>Lemma 3.1.1 (Spirtes et al.)\<close>
(* ---------------------------------------------------------------- *)

definition hop :: "nat \<Rightarrow> node list \<Rightarrow> node set \<Rightarrow> bool" where
  "hop i vs S \<longleftrightarrow>
        d_conn (vs ! i) (vs ! (i + 1)) S \<and>
        (noncoll (vs ! i) (vs ! (i + 1)) (vs ! (i + 1)) \<longrightarrow> vs ! (i + 1) \<notin> S) \<and>
        (collider (vs ! i) (vs ! (i + 1)) (vs ! (i + 2)) \<longrightarrow> vs ! (i + 1) \<in> S)"

definition hopS :: "nat \<Rightarrow> node list \<Rightarrow> node set" where
  "hopS i vs \<equiv> (SOME S. hop i vs S)"

lemma lemma_3_1_1:
  fixes vs :: "node list"
  assumes walk: "walk vs"
      and len:  "length vs \<ge> 2"
      and hops: "\<And>i. i < length vs - 1 \<Longrightarrow> hop i vs (hopS i vs)"
  shows "d_conn (hd vs) (last vs) (\<Union>i<length vs - 1. hopS i vs)"
  sorry

end