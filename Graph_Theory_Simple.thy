theory Graph_Theory_Simple
  imports Main
begin

text \<open>Generic graph-theoretic definitions and d-separation lemmas used
      throughout the project.\<close>

(* ---------------------------------------------------------------- *)
section \<open>Primitive notions\<close>
(* ---------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
subsection \<open>Basic predicates used only by the recursive-blocking theory\<close>
(* ------------------------------------------------------------------------- *)

type_synonym node = nat  \<comment> \<open>or use any other type you prefer\<close>
type_synonym edge = "node \<times> node"
type_synonym path = "node list"    \<comment> \<open>treat a path as a list of vertices\<close>

consts
  Coll        :: "node \<Rightarrow> path \<Rightarrow> bool"          \<comment> \<open>v is collider on p\<close>
  NonC        :: "node \<Rightarrow> path \<Rightarrow> bool"          \<comment> \<open>v is non-collider on p\<close>
  Endpoint    :: "node \<Rightarrow> path \<Rightarrow> bool"
  OnPath      :: "node \<Rightarrow> path \<Rightarrow> bool"
  AfterOnPath :: "node \<Rightarrow> node \<Rightarrow> path \<Rightarrow> bool"
  Halts       :: "node set \<Rightarrow> bool"
  Growsto     :: "node set \<Rightarrow> node set \<Rightarrow> bool"
  StrictSubset:: "node set \<Rightarrow> node set \<Rightarrow> bool"
  Initial     :: "node set"
 (* Adj         :: "node \<Rightarrow> node \<Rightarrow> bool"           \<comment> \<open>directed adjacency\<close>*)
  collider    :: "node \<Rightarrow> node \<Rightarrow> node \<Rightarrow> bool"     \<comment> \<open>middle vertex is a collider\<close>
  noncoll     :: "node \<Rightarrow> node \<Rightarrow> node \<Rightarrow> bool"     \<comment> \<open>middle vertex is a non-collider\<close>

record graph =
  V :: "node set"
  E :: "edge set"

definition Adj :: "graph \<Rightarrow> node \<Rightarrow> node \<Rightarrow> bool" where
  "Adj g x y \<equiv> (x, y) \<in> E g"

text \<open>A *walk* is a (non-empty) list of vertices in which every pair of
      consecutive vertices is adjacent.\<close>
fun walk :: "graph \<Rightarrow> node list \<Rightarrow> bool" where
  "walk _ []         \<longleftrightarrow> False" |
  "walk _ [_]        \<longleftrightarrow> True"  |
  "walk g (x # y # ws) \<longleftrightarrow> Adj g x y \<and> walk g (y # ws)"

(* ---------------------------------------------------------------- *)
section \<open>Activation along a walk\<close>
(* ---------------------------------------------------------------- *)

definition active :: "graph \<Rightarrow> node list \<Rightarrow> node set \<Rightarrow> bool" where
  "active g vs S \<longleftrightarrow>
     walk g vs \<and>
     (let n = length vs in
        (\<forall>i. 0 < i \<and> i + 1 < n \<longrightarrow>
             ((noncoll (vs ! (i - 1)) (vs ! i) (vs ! (i + 1)) \<longrightarrow> vs ! i \<notin> S) \<and>
              (collider (vs ! (i - 1)) (vs ! i) (vs ! (i + 1)) \<longrightarrow> vs ! i \<in> S))))"

definition d_conn :: "graph \<Rightarrow> node \<Rightarrow> node \<Rightarrow> node set \<Rightarrow> bool" where
  "d_conn g x y S \<longleftrightarrow> (\<exists>P. hd P = x \<and> last P = y \<and> active g P S)"

definition DirectedPath :: "graph \<Rightarrow> node \<Rightarrow> node \<Rightarrow> node list \<Rightarrow> bool" where
  "DirectedPath g x y p \<equiv>
     p \<noteq> [] \<and> hd p = x \<and> last p = y \<and>
     (\<forall>i < length p - 1. Adj g (p ! i) (p ! (i + 1)))"

definition Desc :: "graph \<Rightarrow> node \<Rightarrow> node \<Rightarrow> bool" where
  "Desc g x y \<equiv> \<exists>p. DirectedPath g x y p"

definition NoDescInB :: "graph \<Rightarrow> node \<Rightarrow> node set \<Rightarrow> bool" where
  "NoDescInB g c B \<equiv> \<not> (\<exists>d. Desc g c d \<and> d \<in> B)"

definition Blocked :: "graph \<Rightarrow> path \<Rightarrow> node set \<Rightarrow> bool" where
  "Blocked g p B \<equiv> (\<exists>v. NonC v p \<and> v \<in> B) \<or> (\<forall>c. Coll c p \<longrightarrow> NoDescInB g c B)"

definition Path :: "graph \<Rightarrow> node \<Rightarrow> node \<Rightarrow> path \<Rightarrow> bool" where
  "Path g x y p \<longleftrightarrow> hd p = x \<and> last p = y \<and> walk g p"

(* ---------------------------------------------------------------- *)
section \<open>Fundamental helper lemmas (placeholders for now)\<close>
(* ---------------------------------------------------------------- *)

lemma walk_concat_single:
  assumes "walk g (xs @ [v])"
      and "walk g (v # ys)"
  shows   "walk g (xs @ v # ys)"
  sorry

lemma active_append:
  assumes seg1: "active g (xs @ [a]) S1"
      and seg2: "active g (a # ys)  S2"
      and mid:  "(noncoll (last xs) a (hd ys) \<longrightarrow> a \<notin> S2) \<and>
                 (collider (last xs) a (hd ys) \<longrightarrow> a \<in> S1)"
  shows  "active g (xs @ a # ys) (S1 \<union> S2)"
  sorry

lemma d_conn_bridge:
  assumes "d_conn g x a T1"
      and "d_conn g a y T2"
      and "(noncoll x a a \<and> a \<notin> T2) \<or> (collider x a a \<and> a \<in> T1)"
  shows  "d_conn g x y (T1 \<union> T2)"
  sorry

(* ---------------------------------------------------------------- *)
section \<open>Lemma 3.3.1 (Spirtes et al.)\<close>
(* ---------------------------------------------------------------- *)

definition hop :: "graph \<Rightarrow> nat \<Rightarrow> node list \<Rightarrow> node set \<Rightarrow> bool" where
  "hop g i vs S \<longleftrightarrow>
        d_conn g (vs ! i) (vs ! (i + 1)) S \<and>
        (noncoll (vs ! i) (vs ! (i + 1)) (vs ! (i + 1)) \<longrightarrow> vs ! (i + 1) \<notin> S) \<and>
        (collider (vs ! i) (vs ! (i + 1)) (vs ! (i + 2)) \<longrightarrow> vs ! (i + 1) \<in> S)"

definition hopS :: "graph \<Rightarrow> nat \<Rightarrow> node list \<Rightarrow> node set" where
  "hopS g i vs \<equiv> (SOME S. hop g i vs S)"

lemma lemma_3_1_1:
  fixes g :: graph
    and vs :: "node list"
  assumes walk: "walk g vs"
      and len:  "length vs \<ge> 2"
      and hops: "\<And>i. i < length vs - 1 \<Longrightarrow> hop g i vs (hopS g i vs)"
  shows "d_conn g (hd vs) (last vs) (\<Union>i<length vs - 1. hopS g i vs)"
  sorry

end